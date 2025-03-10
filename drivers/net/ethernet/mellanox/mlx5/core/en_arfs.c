/*
 * Copyright (c) 2016, Mellanox Technologies. All rights reserved.
 *
 * This software is available to you under a choice of one of two
 * licenses.  You may choose to be licensed under the terms of the GNU
 * General Public License (GPL) Version 2, available from the file
 * COPYING in the main directory of this source tree, or the
 * OpenIB.org BSD license below:
 *
 *     Redistribution and use in source and binary forms, with or
 *     without modification, are permitted provided that the following
 *     conditions are met:
 *
 *      - Redistributions of source code must retain the above
 *        copyright notice, this list of conditions and the following
 *        disclaimer.
 *
 *      - Redistributions in binary form must reproduce the above
 *        copyright notice, this list of conditions and the following
 *        disclaimer in the documentation and/or other materials
 *        provided with the distribution.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

#include <linux/hash.h>
#include <linux/mlx5/fs.h>
#include <linux/ip.h>
#include <linux/ipv6.h>
#include "en.h"

#define ARFS_HASH_SHIFT BITS_PER_BYTE
#define ARFS_HASH_SIZE BIT(BITS_PER_BYTE)

struct arfs_table {
	struct mlx5e_flow_table  ft;
	struct mlx5_flow_handle	 *default_rule;
	struct hlist_head	 rules_hash[ARFS_HASH_SIZE];
};

enum arfs_type {
	ARFS_IPV4_TCP,
	ARFS_IPV6_TCP,
	ARFS_IPV4_UDP,
	ARFS_IPV6_UDP,
	ARFS_NUM_TYPES,
};

struct mlx5e_arfs_tables {
	struct arfs_table arfs_tables[ARFS_NUM_TYPES];
	/* Protect aRFS rules list */
	spinlock_t                     arfs_lock;
	int                            last_filter_id;
	struct workqueue_struct        *wq;
};

struct arfs_tuple {
	__be16 etype;
	u8     ip_proto;
	union {
		__be32 src_ipv4;
		struct in6_addr src_ipv6;
	};
	union {
		__be32 dst_ipv4;
		struct in6_addr dst_ipv6;
	};
	__be16 src_port;
	__be16 dst_port;
};

struct arfs_rule {
	struct mlx5e_priv	*priv;
	struct work_struct      arfs_work;
	struct mlx5_flow_handle *rule;
	struct hlist_node	hlist;
	int			rxq;
	/* Flow ID passed to ndo_rx_flow_steer */
	int			flow_id;
	/* Filter ID returned by ndo_rx_flow_steer */
	int			filter_id;
	struct arfs_tuple	tuple;
};

#define mlx5e_for_each_arfs_rule(hn, tmp, arfs_tables, i, j) \
	for (i = 0; i < ARFS_NUM_TYPES; i++) \
		mlx5e_for_each_hash_arfs_rule(hn, tmp, arfs_tables[i].rules_hash, j)

#define mlx5e_for_each_hash_arfs_rule(hn, tmp, hash, j) \
	for (j = 0; j < ARFS_HASH_SIZE; j++) \
		hlist_for_each_entry_safe(hn, tmp, &hash[j], hlist)

static enum mlx5_traffic_types arfs_get_tt(enum arfs_type type)
{
	switch (type) {
	case ARFS_IPV4_TCP:
		return MLX5_TT_IPV4_TCP;
	case ARFS_IPV4_UDP:
		return MLX5_TT_IPV4_UDP;
	case ARFS_IPV6_TCP:
		return MLX5_TT_IPV6_TCP;
	case ARFS_IPV6_UDP:
		return MLX5_TT_IPV6_UDP;
	default:
		return -EINVAL;
	}
}

static int arfs_disable(struct mlx5e_flow_steering *fs)
{
	struct mlx5_ttc_table *ttc = mlx5e_fs_get_ttc(fs, false);
	int err, i;

	for (i = 0; i < ARFS_NUM_TYPES; i++) {
		/* Modify ttc rules destination back to their default */
		err = mlx5_ttc_fwd_default_dest(ttc, arfs_get_tt(i));
		if (err) {
			fs_err(fs,
			       "%s: modify ttc[%d] default destination failed, err(%d)\n",
			       __func__, arfs_get_tt(i), err);
			return err;
		}
	}
	return 0;
}

static void arfs_del_rules(struct mlx5e_flow_steering *fs);

int mlx5e_arfs_disable(struct mlx5e_flow_steering *fs)
{
	/* Moving to switchdev mode, fs->arfs is freed by mlx5e_nic_profile
	 * cleanup_rx callback and it is not recreated when
	 * mlx5e_uplink_rep_profile is loaded as mlx5e_create_flow_steering()
	 * is not called by the uplink_rep profile init_rx callback. Thus, if
	 * ntuple is set, moving to switchdev flow will enter this function
	 * with fs->arfs nullified.
	 */
	if (!mlx5e_fs_get_arfs(fs))
		return 0;

	arfs_del_rules(fs);

	return arfs_disable(fs);
}

int mlx5e_arfs_enable(struct mlx5e_flow_steering *fs)
{
	struct mlx5_ttc_table *ttc = mlx5e_fs_get_ttc(fs, false);
	struct mlx5e_arfs_tables *arfs =  mlx5e_fs_get_arfs(fs);
	struct mlx5_flow_destination dest = {};
	int err, i;

	dest.type = MLX5_FLOW_DESTINATION_TYPE_FLOW_TABLE;
	for (i = 0; i < ARFS_NUM_TYPES; i++) {
		dest.ft = arfs->arfs_tables[i].ft.t;
		/* Modify ttc rules destination to point on the aRFS FTs */
		err = mlx5_ttc_fwd_dest(ttc, arfs_get_tt(i), &dest);
		if (err) {
			fs_err(fs, "%s: modify ttc[%d] dest to arfs, failed err(%d)\n",
			       __func__, arfs_get_tt(i), err);
			arfs_disable(fs);
			return err;
		}
	}
	return 0;
}

static void arfs_destroy_table(struct arfs_table *arfs_t)
{
	mlx5_del_flow_rules(arfs_t->default_rule);
	mlx5e_destroy_flow_table(&arfs_t->ft);
}

static void _mlx5e_cleanup_tables(struct mlx5e_flow_steering *fs)
{
	struct mlx5e_arfs_tables *arfs =  mlx5e_fs_get_arfs(fs);
	int i;

	arfs_del_rules(fs);
	destroy_workqueue(arfs->wq);
	for (i = 0; i < ARFS_NUM_TYPES; i++) {
		if (!IS_ERR_OR_NULL(arfs->arfs_tables[i].ft.t))
			arfs_destroy_table(&arfs->arfs_tables[i]);
	}
}

void mlx5e_arfs_destroy_tables(struct mlx5e_flow_steering *fs, bool ntuple)
{
	struct mlx5e_arfs_tables *arfs =  mlx5e_fs_get_arfs(fs);

	if (!ntuple)
		return;

	_mlx5e_cleanup_tables(fs);
	mlx5e_fs_set_arfs(fs, NULL);
	kvfree(arfs);
}

static int arfs_add_default_rule(struct mlx5e_flow_steering *fs,
				 struct mlx5e_rx_res *rx_res,
				 enum arfs_type type)
{
	struct mlx5e_arfs_tables *arfs =  mlx5e_fs_get_arfs(fs);
	struct arfs_table *arfs_t = &arfs->arfs_tables[type];
	struct mlx5_flow_destination dest = {};
	MLX5_DECLARE_FLOW_ACT(flow_act);
	enum mlx5_traffic_types tt;
	int err = 0;

	dest.type = MLX5_FLOW_DESTINATION_TYPE_TIR;
	tt = arfs_get_tt(type);
	if (tt == -EINVAL) {
		fs_err(fs, "%s: bad arfs_type: %d\n", __func__, type);
		return -EINVAL;
	}

	/* FIXME: Must use mlx5_ttc_get_default_dest(),
	 * but can't since TTC default is not setup yet !
	 */
	dest.tir_num = mlx5e_rx_res_get_tirn_rss(rx_res, tt);
	arfs_t->default_rule = mlx5_add_flow_rules(arfs_t->ft.t, NULL,
						   &flow_act,
						   &dest, 1);
	if (IS_ERR(arfs_t->default_rule)) {
		err = PTR_ERR(arfs_t->default_rule);
		arfs_t->default_rule = NULL;
		fs_err(fs, "%s: add rule failed, arfs type=%d\n", __func__, type);
	}

	return err;
}

#define MLX5E_ARFS_NUM_GROUPS	2
#define MLX5E_ARFS_GROUP1_SIZE	(BIT(16) - 1)
#define MLX5E_ARFS_GROUP2_SIZE	BIT(0)
#define MLX5E_ARFS_TABLE_SIZE	(MLX5E_ARFS_GROUP1_SIZE +\
				 MLX5E_ARFS_GROUP2_SIZE)
static int arfs_create_groups(struct mlx5e_flow_table *ft,
			      enum  arfs_type type)
{
	int inlen = MLX5_ST_SZ_BYTES(create_flow_group_in);
	void *outer_headers_c;
	int ix = 0;
	u32 *in;
	int err;
	u8 *mc;

	ft->g = kcalloc(MLX5E_ARFS_NUM_GROUPS,
			sizeof(*ft->g), GFP_KERNEL);
	if (!ft->g)
		return -ENOMEM;

	in = kvzalloc(inlen, GFP_KERNEL);
	if (!in) {
		err = -ENOMEM;
		goto err_free_g;
	}

	mc = MLX5_ADDR_OF(create_flow_group_in, in, match_criteria);
	outer_headers_c = MLX5_ADDR_OF(fte_match_param, mc,
				       outer_headers);
	MLX5_SET_TO_ONES(fte_match_set_lyr_2_4, outer_headers_c, ethertype);
	switch (type) {
	case ARFS_IPV4_TCP:
	case ARFS_IPV6_TCP:
		MLX5_SET_TO_ONES(fte_match_set_lyr_2_4, outer_headers_c, tcp_dport);
		MLX5_SET_TO_ONES(fte_match_set_lyr_2_4, outer_headers_c, tcp_sport);
		break;
	case ARFS_IPV4_UDP:
	case ARFS_IPV6_UDP:
		MLX5_SET_TO_ONES(fte_match_set_lyr_2_4, outer_headers_c, udp_dport);
		MLX5_SET_TO_ONES(fte_match_set_lyr_2_4, outer_headers_c, udp_sport);
		break;
	default:
		err = -EINVAL;
		goto err_free_in;
	}

	switch (type) {
	case ARFS_IPV4_TCP:
	case ARFS_IPV4_UDP:
		MLX5_SET_TO_ONES(fte_match_set_lyr_2_4, outer_headers_c,
				 src_ipv4_src_ipv6.ipv4_layout.ipv4);
		MLX5_SET_TO_ONES(fte_match_set_lyr_2_4, outer_headers_c,
				 dst_ipv4_dst_ipv6.ipv4_layout.ipv4);
		break;
	case ARFS_IPV6_TCP:
	case ARFS_IPV6_UDP:
		memset(MLX5_ADDR_OF(fte_match_set_lyr_2_4, outer_headers_c,
				    src_ipv4_src_ipv6.ipv6_layout.ipv6),
		       0xff, 16);
		memset(MLX5_ADDR_OF(fte_match_set_lyr_2_4, outer_headers_c,
				    dst_ipv4_dst_ipv6.ipv6_layout.ipv6),
		       0xff, 16);
		break;
	default:
		err = -EINVAL;
		goto err_free_in;
	}

	MLX5_SET_CFG(in, match_criteria_enable, MLX5_MATCH_OUTER_HEADERS);
	MLX5_SET_CFG(in, start_flow_index, ix);
	ix += MLX5E_ARFS_GROUP1_SIZE;
	MLX5_SET_CFG(in, end_flow_index, ix - 1);
	ft->g[ft->num_groups] = mlx5_create_flow_group(ft->t, in);
	if (IS_ERR(ft->g[ft->num_groups]))
		goto err_clean_group;
	ft->num_groups++;

	memset(in, 0, inlen);
	MLX5_SET_CFG(in, start_flow_index, ix);
	ix += MLX5E_ARFS_GROUP2_SIZE;
	MLX5_SET_CFG(in, end_flow_index, ix - 1);
	ft->g[ft->num_groups] = mlx5_create_flow_group(ft->t, in);
	if (IS_ERR(ft->g[ft->num_groups]))
		goto err_clean_group;
	ft->num_groups++;

	kvfree(in);
	return 0;

err_clean_group:
	err = PTR_ERR(ft->g[ft->num_groups]);
	ft->g[ft->num_groups] = NULL;
err_free_in:
	kvfree(in);
err_free_g:
	kfree(ft->g);
	ft->g = NULL;
	return err;
}

static int arfs_create_table(struct mlx5e_flow_steering *fs,
			     struct mlx5e_rx_res *rx_res,
			     enum arfs_type type)
{
	struct mlx5_flow_namespace *ns = mlx5e_fs_get_ns(fs, false);
	struct mlx5e_arfs_tables *arfs = mlx5e_fs_get_arfs(fs);
	struct mlx5e_flow_table *ft = &arfs->arfs_tables[type].ft;
	struct mlx5_flow_table_attr ft_attr = {};
	int err;

	ft->num_groups = 0;

	ft_attr.max_fte = MLX5E_ARFS_TABLE_SIZE;
	ft_attr.level = MLX5E_ARFS_FT_LEVEL;
	ft_attr.prio = MLX5E_NIC_PRIO;

	ft->t = mlx5_create_flow_table(ns, &ft_attr);
	if (IS_ERR(ft->t)) {
		err = PTR_ERR(ft->t);
		ft->t = NULL;
		return err;
	}

	err = arfs_create_groups(ft, type);
	if (err)
		goto err;

	err = arfs_add_default_rule(fs, rx_res,  type);
	if (err)
		goto err;

	return 0;
err:
	mlx5e_destroy_flow_table(ft);
	return err;
}

int mlx5e_arfs_create_tables(struct mlx5e_flow_steering *fs,
			     struct mlx5e_rx_res *rx_res, bool ntuple)
{
	struct mlx5e_arfs_tables *arfs;
	int err = -ENOMEM;
	int i;

	if (!ntuple)
		return 0;

	arfs = kvzalloc(sizeof(*arfs), GFP_KERNEL);
	if (!arfs)
		return -ENOMEM;

	spin_lock_init(&arfs->arfs_lock);
	arfs->wq = create_singlethread_workqueue("mlx5e_arfs");
	if (!arfs->wq)
		goto err;

	mlx5e_fs_set_arfs(fs, arfs);

	for (i = 0; i < ARFS_NUM_TYPES; i++) {
		err = arfs_create_table(fs, rx_res, i);
		if (err)
			goto err_des;
	}
	return 0;

err_des:
	_mlx5e_cleanup_tables(fs);
err:
	mlx5e_fs_set_arfs(fs, NULL);
	kvfree(arfs);
	return err;
}

#define MLX5E_ARFS_EXPIRY_QUOTA 60

static void arfs_may_expire_flow(struct mlx5e_priv *priv)
{
	struct mlx5e_arfs_tables *arfs = mlx5e_fs_get_arfs(priv->fs);
	struct arfs_rule *arfs_rule;
	struct hlist_node *htmp;
	HLIST_HEAD(del_list);
	int quota = 0;
	int i;
	int j;

	spin_lock_bh(&arfs->arfs_lock);
	mlx5e_for_each_arfs_rule(arfs_rule, htmp, arfs->arfs_tables, i, j) {
		if (!work_pending(&arfs_rule->arfs_work) &&
		    rps_may_expire_flow(priv->netdev,
					arfs_rule->rxq, arfs_rule->flow_id,
					arfs_rule->filter_id)) {
			hlist_del_init(&arfs_rule->hlist);
			hlist_add_head(&arfs_rule->hlist, &del_list);
			if (quota++ > MLX5E_ARFS_EXPIRY_QUOTA)
				break;
		}
	}
	spin_unlock_bh(&arfs->arfs_lock);
	hlist_for_each_entry_safe(arfs_rule, htmp, &del_list, hlist) {
		if (arfs_rule->rule)
			mlx5_del_flow_rules(arfs_rule->rule);
		hlist_del(&arfs_rule->hlist);
		kfree(arfs_rule);
	}
}

static void arfs_del_rules(struct mlx5e_flow_steering *fs)
{
	struct mlx5e_arfs_tables *arfs = mlx5e_fs_get_arfs(fs);
	struct hlist_node *htmp;
	struct arfs_rule *rule;
	HLIST_HEAD(del_list);
	int i;
	int j;

	spin_lock_bh(&arfs->arfs_lock);
	mlx5e_for_each_arfs_rule(rule, htmp, arfs->arfs_tables, i, j) {
		hlist_del_init(&rule->hlist);
		hlist_add_head(&rule->hlist, &del_list);
	}
	spin_unlock_bh(&arfs->arfs_lock);

	hlist_for_each_entry_safe(rule, htmp, &del_list, hlist) {
		cancel_work_sync(&rule->arfs_work);
		if (rule->rule)
			mlx5_del_flow_rules(rule->rule);
		hlist_del(&rule->hlist);
		kfree(rule);
	}
}

static struct hlist_head *
arfs_hash_bucket(struct arfs_table *arfs_t, __be16 src_port,
		 __be16 dst_port)
{
	unsigned long l;
	int bucket_idx;

	l = (__force unsigned long)src_port |
	    ((__force unsigned long)dst_port << 2);

	bucket_idx = hash_long(l, ARFS_HASH_SHIFT);

	return &arfs_t->rules_hash[bucket_idx];
}

static struct arfs_table *arfs_get_table(struct mlx5e_arfs_tables *arfs,
					 u8 ip_proto, __be16 etype)
{
	if (etype == htons(ETH_P_IP) && ip_proto == IPPROTO_TCP)
		return &arfs->arfs_tables[ARFS_IPV4_TCP];
	if (etype == htons(ETH_P_IP) && ip_proto == IPPROTO_UDP)
		return &arfs->arfs_tables[ARFS_IPV4_UDP];
	if (etype == htons(ETH_P_IPV6) && ip_proto == IPPROTO_TCP)
		return &arfs->arfs_tables[ARFS_IPV6_TCP];
	if (etype == htons(ETH_P_IPV6) && ip_proto == IPPROTO_UDP)
		return &arfs->arfs_tables[ARFS_IPV6_UDP];

	return NULL;
}

static struct mlx5_flow_handle *arfs_add_rule(struct mlx5e_priv *priv,
					      struct arfs_rule *arfs_rule)
{
	struct mlx5e_arfs_tables *arfs = mlx5e_fs_get_arfs(priv->fs);
	struct arfs_tuple *tuple = &arfs_rule->tuple;
	struct mlx5_flow_handle *rule = NULL;
	struct mlx5_flow_destination dest = {};
	MLX5_DECLARE_FLOW_ACT(flow_act);
	struct arfs_table *arfs_table;
	struct mlx5_flow_spec *spec;
	struct mlx5_flow_table *ft;
	int err = 0;

	spec = kvzalloc(sizeof(*spec), GFP_KERNEL);
	if (!spec) {
		err = -ENOMEM;
		goto out;
	}
	spec->match_criteria_enable = MLX5_MATCH_OUTER_HEADERS;
	MLX5_SET_TO_ONES(fte_match_param, spec->match_criteria,
			 outer_headers.ethertype);
	MLX5_SET(fte_match_param, spec->match_value, outer_headers.ethertype,
		 ntohs(tuple->etype));
	arfs_table = arfs_get_table(arfs, tuple->ip_proto, tuple->etype);
	if (!arfs_table) {
		err = -EINVAL;
		goto out;
	}

	ft = arfs_table->ft.t;
	if (tuple->ip_proto == IPPROTO_TCP) {
		MLX5_SET_TO_ONES(fte_match_param, spec->match_criteria,
				 outer_headers.tcp_dport);
		MLX5_SET_TO_ONES(fte_match_param, spec->match_criteria,
				 outer_headers.tcp_sport);
		MLX5_SET(fte_match_param, spec->match_value, outer_headers.tcp_dport,
			 ntohs(tuple->dst_port));
		MLX5_SET(fte_match_param, spec->match_value, outer_headers.tcp_sport,
			 ntohs(tuple->src_port));
	} else {
		MLX5_SET_TO_ONES(fte_match_param, spec->match_criteria,
				 outer_headers.udp_dport);
		MLX5_SET_TO_ONES(fte_match_param, spec->match_criteria,
				 outer_headers.udp_sport);
		MLX5_SET(fte_match_param, spec->match_value, outer_headers.udp_dport,
			 ntohs(tuple->dst_port));
		MLX5_SET(fte_match_param, spec->match_value, outer_headers.udp_sport,
			 ntohs(tuple->src_port));
	}
	if (tuple->etype == htons(ETH_P_IP)) {
		memcpy(MLX5_ADDR_OF(fte_match_param, spec->match_value,
				    outer_headers.src_ipv4_src_ipv6.ipv4_layout.ipv4),
		       &tuple->src_ipv4,
		       4);
		memcpy(MLX5_ADDR_OF(fte_match_param, spec->match_value,
				    outer_headers.dst_ipv4_dst_ipv6.ipv4_layout.ipv4),
		       &tuple->dst_ipv4,
		       4);
		MLX5_SET_TO_ONES(fte_match_param, spec->match_criteria,
				 outer_headers.src_ipv4_src_ipv6.ipv4_layout.ipv4);
		MLX5_SET_TO_ONES(fte_match_param, spec->match_criteria,
				 outer_headers.dst_ipv4_dst_ipv6.ipv4_layout.ipv4);
	} else {
		memcpy(MLX5_ADDR_OF(fte_match_param, spec->match_value,
				    outer_headers.src_ipv4_src_ipv6.ipv6_layout.ipv6),
		       &tuple->src_ipv6,
		       16);
		memcpy(MLX5_ADDR_OF(fte_match_param, spec->match_value,
				    outer_headers.dst_ipv4_dst_ipv6.ipv6_layout.ipv6),
		       &tuple->dst_ipv6,
		       16);
		memset(MLX5_ADDR_OF(fte_match_param, spec->match_criteria,
				    outer_headers.src_ipv4_src_ipv6.ipv6_layout.ipv6),
		       0xff,
		       16);
		memset(MLX5_ADDR_OF(fte_match_param, spec->match_criteria,
				    outer_headers.dst_ipv4_dst_ipv6.ipv6_layout.ipv6),
		       0xff,
		       16);
	}
	dest.type = MLX5_FLOW_DESTINATION_TYPE_TIR;
	dest.tir_num = mlx5e_rx_res_get_tirn_direct(priv->rx_res, arfs_rule->rxq);
	rule = mlx5_add_flow_rules(ft, spec, &flow_act, &dest, 1);
	if (IS_ERR(rule)) {
		err = PTR_ERR(rule);
		priv->channel_stats[arfs_rule->rxq]->rq.arfs_err++;
		netdev_dbg(priv->netdev,
			   "%s: add rule(filter id=%d, rq idx=%d, ip proto=0x%x) failed,err=%d\n",
			   __func__, arfs_rule->filter_id, arfs_rule->rxq,
			   tuple->ip_proto, err);
	}

out:
	kvfree(spec);
	return err ? ERR_PTR(err) : rule;
}

static void arfs_modify_rule_rq(struct mlx5e_priv *priv,
				struct mlx5_flow_handle *rule, u16 rxq)
{
	struct mlx5_flow_destination dst = {};
	int err = 0;

	dst.type = MLX5_FLOW_DESTINATION_TYPE_TIR;
	dst.tir_num = mlx5e_rx_res_get_tirn_direct(priv->rx_res, rxq);
	err =  mlx5_modify_rule_destination(rule, &dst, NULL);
	if (err)
		netdev_warn(priv->netdev,
			    "Failed to modify aRFS rule destination to rq=%d\n", rxq);
}

static void arfs_handle_work(struct work_struct *work)
{
	struct arfs_rule *arfs_rule = container_of(work,
						   struct arfs_rule,
						   arfs_work);
	struct mlx5e_priv *priv = arfs_rule->priv;
	struct mlx5e_arfs_tables *arfs;
	struct mlx5_flow_handle *rule;

	arfs = mlx5e_fs_get_arfs(priv->fs);
	mutex_lock(&priv->state_lock);
	if (!test_bit(MLX5E_STATE_OPENED, &priv->state)) {
		spin_lock_bh(&arfs->arfs_lock);
		hlist_del(&arfs_rule->hlist);
		spin_unlock_bh(&arfs->arfs_lock);

		mutex_unlock(&priv->state_lock);
		kfree(arfs_rule);
		goto out;
	}
	mutex_unlock(&priv->state_lock);

	if (!arfs_rule->rule) {
		rule = arfs_add_rule(priv, arfs_rule);
		if (IS_ERR(rule))
			goto out;
		arfs_rule->rule = rule;
	} else {
		arfs_modify_rule_rq(priv, arfs_rule->rule,
				    arfs_rule->rxq);
	}
out:
	arfs_may_expire_flow(priv);
}

static struct arfs_rule *arfs_alloc_rule(struct mlx5e_priv *priv,
					 struct arfs_table *arfs_t,
					 const struct flow_keys *fk,
					 u16 rxq, u32 flow_id)
{
	struct mlx5e_arfs_tables *arfs =  mlx5e_fs_get_arfs(priv->fs);
	struct arfs_rule *rule;
	struct arfs_tuple *tuple;

	rule = kzalloc(sizeof(*rule), GFP_ATOMIC);
	if (!rule)
		return NULL;

	rule->priv = priv;
	rule->rxq = rxq;
	INIT_WORK(&rule->arfs_work, arfs_handle_work);

	tuple = &rule->tuple;
	tuple->etype = fk->basic.n_proto;
	tuple->ip_proto = fk->basic.ip_proto;
	if (tuple->etype == htons(ETH_P_IP)) {
		tuple->src_ipv4 = fk->addrs.v4addrs.src;
		tuple->dst_ipv4 = fk->addrs.v4addrs.dst;
	} else {
		memcpy(&tuple->src_ipv6, &fk->addrs.v6addrs.src,
		       sizeof(struct in6_addr));
		memcpy(&tuple->dst_ipv6, &fk->addrs.v6addrs.dst,
		       sizeof(struct in6_addr));
	}
	tuple->src_port = fk->ports.src;
	tuple->dst_port = fk->ports.dst;

	rule->flow_id = flow_id;
	rule->filter_id = arfs->last_filter_id++ % RPS_NO_FILTER;

	hlist_add_head(&rule->hlist,
		       arfs_hash_bucket(arfs_t, tuple->src_port,
					tuple->dst_port));
	return rule;
}

static bool arfs_cmp(const struct arfs_tuple *tuple, const struct flow_keys *fk)
{
	if (tuple->src_port != fk->ports.src || tuple->dst_port != fk->ports.dst)
		return false;
	if (tuple->etype != fk->basic.n_proto)
		return false;
	if (tuple->etype == htons(ETH_P_IP))
		return tuple->src_ipv4 == fk->addrs.v4addrs.src &&
		       tuple->dst_ipv4 == fk->addrs.v4addrs.dst;
	if (tuple->etype == htons(ETH_P_IPV6))
		return !memcmp(&tuple->src_ipv6, &fk->addrs.v6addrs.src,
			       sizeof(struct in6_addr)) &&
		       !memcmp(&tuple->dst_ipv6, &fk->addrs.v6addrs.dst,
			       sizeof(struct in6_addr));
	return false;
}

static struct arfs_rule *arfs_find_rule(struct arfs_table *arfs_t,
					const struct flow_keys *fk)
{
	struct arfs_rule *arfs_rule;
	struct hlist_head *head;

	head = arfs_hash_bucket(arfs_t, fk->ports.src, fk->ports.dst);
	hlist_for_each_entry(arfs_rule, head, hlist) {
		if (arfs_cmp(&arfs_rule->tuple, fk))
			return arfs_rule;
	}

	return NULL;
}

int mlx5e_rx_flow_steer(struct net_device *dev, const struct sk_buff *skb,
			u16 rxq_index, u32 flow_id)
{
	struct mlx5e_priv *priv = netdev_priv(dev);
	struct mlx5e_arfs_tables *arfs;
	struct arfs_rule *arfs_rule;
	struct arfs_table *arfs_t;
	struct flow_keys fk;

	arfs =  mlx5e_fs_get_arfs(priv->fs);
	if (!skb_flow_dissect_flow_keys(skb, &fk, 0))
		return -EPROTONOSUPPORT;

	if (fk.basic.n_proto != htons(ETH_P_IP) &&
	    fk.basic.n_proto != htons(ETH_P_IPV6))
		return -EPROTONOSUPPORT;

	if (skb->encapsulation)
		return -EPROTONOSUPPORT;

	arfs_t = arfs_get_table(arfs, fk.basic.ip_proto, fk.basic.n_proto);
	if (!arfs_t)
		return -EPROTONOSUPPORT;

	spin_lock_bh(&arfs->arfs_lock);
	arfs_rule = arfs_find_rule(arfs_t, &fk);
	if (arfs_rule) {
		if (arfs_rule->rxq == rxq_index) {
			spin_unlock_bh(&arfs->arfs_lock);
			return arfs_rule->filter_id;
		}
		arfs_rule->rxq = rxq_index;
	} else {
		arfs_rule = arfs_alloc_rule(priv, arfs_t, &fk, rxq_index, flow_id);
		if (!arfs_rule) {
			spin_unlock_bh(&arfs->arfs_lock);
			return -ENOMEM;
		}
	}
	queue_work(arfs->wq, &arfs_rule->arfs_work);
	spin_unlock_bh(&arfs->arfs_lock);
	return arfs_rule->filter_id;
}


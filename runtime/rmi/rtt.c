/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <addr_list.h>
#include <assert.h>
#include <buffer.h>
#include <debug.h>
#include <dev_granule.h>
#include <errno.h>
#include <granule.h>
#include <measurement.h>
#include <planes.h>
#include <realm.h>
#include <ripas.h>
#include <rtt_internal.h>
#include <s2tt.h>
#include <s2tt_ap.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <smmuv3.h>
#include <status.h>
#include <stddef.h>
/* coverity[unnecessary_header:SUPPRESS] */
#include <string.h>
#include <xlat_defs.h>
#include <xlat_tables.h>

typedef void (*tlb_handler_t)(const struct s2tt_context *s2tt_ctx,
			      struct rd *rd, unsigned long addr, long level);
typedef void (*tlb_handler_per_vmids_t)(struct rd *rd, unsigned long addr, long level);

bool validate_map_addr(unsigned long map_addr,
		       long level,
		       struct rd *rd)
{
	return ((map_addr < realm_ipa_size(rd)) &&
		s2tte_is_addr_lvl_aligned(&rd->s2_ctx[PRIMARY_S2_CTX_ID],
					  map_addr, level));
}

/*
 * Reject aliases and lock the DELEGATED granule after the locked RD and leaf
 * RTT. The lookup stabilizes its own region; return a tracking-aware RMI result.
 */
unsigned long find_lock_rtt_backing_granule(struct granule *g_rd,
					    const struct s2tt_walk *wi,
					    unsigned long backing_addr,
					    struct granule **g_backing)
{
	assert((g_rd != NULL) && LOCKED(g_rd));
	assert(granule_get_state(g_rd) == GRANULE_STATE_RD);
	assert(wi != NULL);
	assert((wi->g_llt != NULL) && LOCKED(wi->g_llt));
	assert(granule_get_state(wi->g_llt) == GRANULE_STATE_RTT);
	assert(g_backing != NULL);
	*g_backing = NULL;

	if ((backing_addr == tr_granule_addr(g_rd)) ||
	    (backing_addr == tr_granule_addr(wi->g_llt))) {
		return RMI_ERROR_INPUT;
	}

	return tr_find_lock_granule(backing_addr,
			GRANULE_SIZE, GRANULE_STATE_DELEGATED, g_backing);
}

/*
 * Structure commands can operate on all RTTs except for the root RTT so
 * the minimal valid level is the stage 2 starting level + 1.
 */
static bool validate_rtt_structure_cmds(unsigned long map_addr,
					long level,
					struct rd *rd)
{
	int min_level = realm_rtt_starting_level(rd) + 1;

	if ((level < min_level) || (level > S2TT_PAGE_LEVEL)) {
		return false;
	}
	return validate_map_addr(map_addr, level - 1L, rd);
}

/*
 * Entry commands can operate on any entry so the minimal valid level is the
 * stage 2 starting level.
 */
static bool validate_rtt_entry_cmds(unsigned long map_addr,
				    long level,
				    struct rd *rd)
{
	if ((level < realm_rtt_starting_level(rd)) ||
	    (level > S2TT_PAGE_LEVEL)) {
		return false;
	}
	return validate_map_addr(map_addr, level, rd);
}

unsigned long default_protected_ap(struct s2tt_context *s2_ctx)
{
	return s2tte_update_prot_ap(s2_ctx, 0UL,
				    S2TTE_DEF_BASE_PERM_IDX,
				    S2TTE_DEF_PROT_OVERLAY_IDX);
}

static bool validate_aux_rtt_args(struct rd *rd, unsigned long s2tt_idx,
				  unsigned long map_addr)
{
	/*
	 * For an auxiliary mapping:
	 *   - The address must be in the PAR.
	 *   - A tree per plane must set on the realm configuration.
	 *   - The tree index must be in the right range.
	 */
	if ((!addr_in_par(rd, map_addr)) || (!rd->rtt_tree_pp) ||
	    (s2tt_idx == (unsigned long)PRIMARY_S2_CTX_ID) ||
	    (s2tt_idx >= (unsigned long)realm_num_s2_contexts(rd))) {
			return false;
	}

	return true;
}

/*
 * Helper function to invalidate a page or block at address @map_addr and @level
 * for all the valid S2 translation contexts on the realm @rd.
 */
static void invalidate_page_block_per_vmids(struct rd *rd, unsigned long map_addr, long level)
{
	unsigned int vmid_list[MAX_S2_CTXS];
	unsigned int nvmids = realm_num_planes(rd);

	for (unsigned int i = 0U; i < nvmids; i++) {
		vmid_list[i] = plane_to_s2_context(rd, i)->vmid;
	}

	s2tt_invalidate_page_block_per_vmids(s2tt_lpa2_enabled(&rd->s2_ctx[PRIMARY_S2_CTX_ID]),
						vmid_list, nvmids, map_addr, level);

	if (rd->da_enabled) {
		int ret = smmuv3_inv_at_level_per_vmids(vmid_list, nvmids, map_addr,
							level, 1UL, true,
							&rd->smmu_cmd_sync);

		if (ret != 0) {
			ERROR("smmuv3_inv_at_level_per_vmids(0x%lx %ld) error %d\n",
				map_addr, level, ret);
			panic();
		}
	}
}

/*
 * Helper function to invalidate the pages in a block at address @map_addr
 * for all the valid S2 translation contexts on the realm @rd.
 */
static void invalidate_pages_in_block_for_contexts(struct rd *rd, unsigned long map_addr,
						   long level)
{
	unsigned int vmid_list[MAX_S2_CTXS];
	unsigned int nvmids = realm_num_planes(rd);

	for (unsigned int i = 0U; i < nvmids; i++) {
		vmid_list[i] = plane_to_s2_context(rd, i)->vmid;
	}

	s2tt_invalidate_pages_in_block_per_vmids(s2tt_lpa2_enabled(&rd->s2_ctx[PRIMARY_S2_CTX_ID]),
							vmid_list, nvmids, map_addr);

	if (rd->da_enabled) {
		int ret = smmuv3_inv_at_level_per_vmids(vmid_list, nvmids, map_addr,
							level, S2TTES_PER_S2TT, false,
							&rd->smmu_cmd_sync);

		if (ret != 0) {
			ERROR("smmuv3_inv_at_level_per_vmids(0x%lx %ld) error %d\n",
				map_addr, level, ret);
			panic();
		}
	}
}

/*
 * Helper function to invalidate a page or block at address @map_addr and @level.
 */
static void invalidate_page_block(const struct s2tt_context *s2_ctx,
				  struct rd *rd, unsigned long map_addr, long level)
{
	s2tt_invalidate_page_block(s2tt_lpa2_enabled(s2_ctx), s2_ctx->vmid, map_addr,
				   level);

	if (rd->da_enabled) {
		int ret = smmuv3_inv_at_level(s2_ctx->vmid, map_addr, level, 1UL, true,
						&rd->smmu_cmd_sync);

		if (ret != 0) {
			ERROR("smmuv3_inv_at_level(0x%x 0x%lx %ld) error %d\n",
				s2_ctx->vmid, map_addr, level, ret);
			panic();
		}
	}
}

/*
 * Helper function to invalidate pages in block at address @map_addr and @level.
 */
static void invalidate_pages_in_block(const struct s2tt_context *s2_ctx,
				      struct rd *rd, unsigned long map_addr, long level)
{
	(void)level;

	s2tt_invalidate_pages_in_block(s2tt_lpa2_enabled(s2_ctx), s2_ctx->vmid,
				      map_addr);

	if (rd->da_enabled) {
		int ret = smmuv3_inv_at_level(s2_ctx->vmid, map_addr, level,
						S2TTES_PER_S2TT, false,
						&rd->smmu_cmd_sync);
		if (ret != 0) {
			ERROR("smmuv3_inv_at_level(0x%x 0x%lx %ld) error %d\n",
				s2_ctx->vmid, map_addr, level, ret);
			panic();
		}
	}
}

/*
 * Create a primary or auxiliary RTT, returning the command's RMI result.
 * Lock RD, then follow RTT hierarchy order before locking the new table's
 * DELEGATED granule. Each lookup stabilizes its own tracking region.
 */
static unsigned long rtt_create(unsigned long rd_addr,
				unsigned long rtt_addr,
				unsigned long map_addr,
				unsigned long ulevel,
				unsigned long s2tt_index,
				bool aux)
{
	struct granule *g_rd;
	struct granule *g_tbl = NULL;
	struct rd *rd;
	struct s2tt_walk wi;
	unsigned long *s2tt, *parent_s2tt, parent_s2tte;
	long level = (long)ulevel;
	unsigned long ret;
	struct s2tt_context *s2_ctx;
	unsigned int rtt_err_code = (aux ? RMI_ERROR_RTT_AUX : RMI_ERROR_RTT);

	ret = tr_find_lock_granule(rd_addr, GRANULE_SIZE, GRANULE_STATE_RD, &g_rd);
	if (ret != RMI_SUCCESS) {
		return ret;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_rtt_structure_cmds(map_addr, level, rd)) {
		ret = RMI_ERROR_INPUT;
		goto out_unmap_rd;
	}

	if (aux) {
		if (!validate_aux_rtt_args(rd, s2tt_index, map_addr)) {
			ret = RMI_ERROR_INPUT;
			goto out_unmap_rd;
		}
		s2_ctx = &rd->s2_ctx[s2tt_index];
	} else {
		s2_ctx = &rd->s2_ctx[PRIMARY_S2_CTX_ID];
	}

	if (rtt_addr >= s2_ctx->s2oa_limit) {
		ret = RMI_ERROR_INPUT;
		goto out_unmap_rd;
	}

	/* Lock the RTT hierarchy before claiming the delegated table granule. */
	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	s2tt_walk_lock_unlock(s2_ctx, map_addr, level - 1L, &wi);
	if (wi.last_level < (level - 1L)) {
		ret = pack_return_code_level(rtt_err_code, (unsigned char)wi.last_level);
		goto out_unlock_llt;
	}

	ret = find_lock_rtt_backing_granule(g_rd, &wi, rtt_addr, &g_tbl);
	if (ret != RMI_SUCCESS) {
		goto out_unlock_llt;
	}

	parent_s2tt = buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx->mecid);
	assert(parent_s2tt != NULL);

	parent_s2tte = s2tte_read(&parent_s2tt[wi.index]);
	/* No need to memzero as the table creation does not rely on this */
	s2tt = buffer_granule_mecid_map(g_tbl, SLOT_RTT2, s2_ctx->mecid);
	assert(s2tt != NULL);

	if (s2tte_is_unassigned_empty(s2_ctx, parent_s2tte)) {
		s2tt_init_unassigned_empty(s2_ctx, s2tt, parent_s2tte);

		/*
		 * Atomically increase the refcount of the parent, the granule
		 * was locked while table walking and hand-over-hand locking.
		 * Acquire/release semantics not required because the table is
		 * accessed always locked.
		 */
		atomic_granule_get(wi.g_llt);

	} else if (s2tte_is_unassigned_ram(s2_ctx, parent_s2tte)) {
		s2tt_init_unassigned_ram(s2_ctx, s2tt, parent_s2tte);
		atomic_granule_get(wi.g_llt);

	} else if (s2tte_is_unassigned_ns(s2_ctx, parent_s2tte)) {
		s2tt_init_unassigned_ns(s2_ctx, s2tt, parent_s2tte);
		atomic_granule_get(wi.g_llt);

	} else if (s2tte_is_unassigned_destroyed(s2_ctx, parent_s2tte)) {
		s2tt_init_unassigned_destroyed(s2_ctx, s2tt, parent_s2tte);
		atomic_granule_get(wi.g_llt);

	} else if (s2tte_is_assigned_destroyed(s2_ctx, parent_s2tte,
					       level - 1L)) {
		unsigned long block_pa;

		/*
		 * We should observe parent assigned s2tte only when
		 * we create tables above this level.
		 */
		assert(level > S2TT_MIN_BLOCK_LEVEL);

		block_pa = s2tte_pa(s2_ctx, parent_s2tte, level - 1L);

		s2tt_init_assigned_destroyed(s2_ctx, s2tt, block_pa, level,
					     parent_s2tte);

		/*
		 * Increase the refcount to mark the granule as in-use. refcount
		 * is incremented by S2TTES_PER_S2TT (ref RTT unfolding).
		 */
		granule_refcount_inc(g_tbl, (unsigned short)S2TTES_PER_S2TT);

	} else if (s2tte_is_assigned_empty(s2_ctx, parent_s2tte, level - 1L)) {
		unsigned long block_pa;

		/*
		 * We should observe parent assigned s2tte only when
		 * we create tables above this level.
		 */
		assert(level > S2TT_MIN_BLOCK_LEVEL);

		block_pa = s2tte_pa(s2_ctx, parent_s2tte, level - 1L);

		s2tt_init_assigned_empty(s2_ctx, s2tt, block_pa, level,
					 parent_s2tte);

		/*
		 * Increase the refcount to mark the granule as in-use. refcount
		 * is incremented by S2TTES_PER_S2TT (ref RTT unfolding).
		 */
		granule_refcount_inc(g_tbl, (unsigned short)S2TTES_PER_S2TT);

	} else if (s2tte_is_assigned_ram(s2_ctx, parent_s2tte, level - 1L)) {
		unsigned long block_pa;

		/*
		 * We should observe parent valid s2tte only when
		 * we create tables above this level.
		 */
		assert(level > S2TT_MIN_BLOCK_LEVEL);

		/*
		 * Break before make. This may cause spurious S2 aborts.
		 */
		s2tte_write(&parent_s2tt[wi.index], 0UL);
		if (s2_ctx->indirect_s2ap) {
			assert(!rd->rtt_tree_pp);

			/* Invalidate TLBs for all Plane VMIDs */
			invalidate_page_block_per_vmids(rd, map_addr, level);
		} else {
			invalidate_page_block(s2_ctx, rd, map_addr, level);
		}

		block_pa = s2tte_pa(s2_ctx, parent_s2tte, level - 1L);

		s2tt_init_assigned_ram(s2_ctx, s2tt, block_pa, level,
					parent_s2tte);
		/*
		 * Increase the refcount to mark the granule as in-use. refcount
		 * is incremented by S2TTES_PER_S2TT (ref RTT unfolding).
		 */
		granule_refcount_inc(g_tbl, (unsigned short)S2TTES_PER_S2TT);

	} else if (s2tte_is_assigned_ns(s2_ctx, parent_s2tte, level - 1L)) {
		unsigned long block_pa;

		/*
		 * We should observe parent assigned_ns s2tte only when
		 * we create tables above this level.
		 */
		assert(level > S2TT_MIN_BLOCK_LEVEL);

		/*
		 * Break before make. This may cause spurious S2 aborts.
		 */
		s2tte_write(&parent_s2tt[wi.index], 0UL);
		if (s2_ctx->indirect_s2ap) {
			assert(!rd->rtt_tree_pp);

			/* Invalidate TLBs for all Plane VMIDs */
			invalidate_page_block_per_vmids(rd, map_addr, level);
		} else {
			invalidate_page_block(s2_ctx, rd, map_addr, level);
		}

		block_pa = s2tte_pa(s2_ctx, parent_s2tte, level - 1L);

		s2tt_init_assigned_ns(s2_ctx, s2tt, parent_s2tte,
				      block_pa, level, parent_s2tte);

		/*
		 * Increment the refcount on the parent for the new RTT we are
		 * about to add. The NS block entry doesn't have a refcount
		 * on the parent RTT.
		 */
		atomic_granule_get(wi.g_llt);

	} else if (s2tte_is_assigned_dev_empty(s2_ctx, parent_s2tte, level - 1L)) {
		unsigned long block_pa;

		/*
		 * We should observe parent assigned s2tte only when
		 * we create tables above this level.
		 */
		assert(level > S2TT_MIN_DEV_BLOCK_LEVEL);

		block_pa = s2tte_pa(s2_ctx, parent_s2tte, level - 1L);

		s2tt_init_assigned_dev_empty(s2_ctx, s2tt, block_pa, level, parent_s2tte);

		/*
		 * Increase the refcount to mark the granule as in-use. refcount
		 * is incremented by S2TTES_PER_S2TT (ref RTT unfolding).
		 */
		granule_refcount_inc(g_tbl, (unsigned short)S2TTES_PER_S2TT);

	} else if (s2tte_is_assigned_dev_destroyed(s2_ctx, parent_s2tte, level - 1L)) {
		unsigned long block_pa;

		/*
		 * We should observe parent assigned s2tte only when
		 * we create tables above this level.
		 */
		assert(level > S2TT_MIN_DEV_BLOCK_LEVEL);

		block_pa = s2tte_pa(s2_ctx, parent_s2tte, level - 1L);

		s2tt_init_assigned_dev_destroyed(s2_ctx, s2tt, block_pa, level, parent_s2tte);

		/*
		 * Increase the refcount to mark the granule as in-use. refcount
		 * is incremented by S2TTES_PER_S2TT (ref RTT unfolding).
		 */
		granule_refcount_inc(g_tbl, (unsigned short)S2TTES_PER_S2TT);

	} else if (s2tte_is_assigned_dev_dev(s2_ctx, parent_s2tte, level - 1L)) {
		unsigned long block_pa;

		/*
		 * We should observe parent valid s2tte only when
		 * we create tables above this level.
		 */
		assert(level > S2TT_MIN_DEV_BLOCK_LEVEL);

		/*
		 * Break before make. This may cause spurious S2 aborts.
		 */
		s2tte_write(&parent_s2tt[wi.index], 0UL);

		invalidate_page_block(s2_ctx, rd, map_addr, level);

		block_pa = s2tte_pa(s2_ctx, parent_s2tte, level - 1L);

		s2tt_init_assigned_dev_dev(s2_ctx, s2tt, parent_s2tte, block_pa, level,
					   parent_s2tte);

		/*
		 * Increase the refcount to mark the granule as in-use. refcount
		 * is incremented by S2TTES_PER_S2TT (ref RTT unfolding).
		 */
		granule_refcount_inc(g_tbl, (unsigned short)S2TTES_PER_S2TT);

	} else if (s2tte_is_table(s2_ctx, parent_s2tte, level - 1L)) {
		ret = pack_return_code_level(rtt_err_code, (unsigned char)(level - 1L));
		goto out_unmap_table;

	} else {
		assert(false);
	}

	ret = RMI_SUCCESS;

	parent_s2tte = s2tte_create_table(s2_ctx, rtt_addr, level - 1L);
	s2tte_write(&parent_s2tt[wi.index], parent_s2tte);

out_unmap_table:
	buffer_unmap(s2tt);
	buffer_unmap(parent_s2tt);
out_unlock_llt:
	granule_unlock(wi.g_llt);

	if (g_tbl == NULL) {
		goto out_unmap_rd;
	}

	if (ret == RMI_SUCCESS) {
		granule_unlock_transition(g_tbl, GRANULE_STATE_RTT);
	} else {
		granule_unlock(g_tbl);
	}

out_unmap_rd:
	buffer_unmap(rd);
	granule_unlock(g_rd);
	return ret;
}

void smc_rtt_create(unsigned long rd_addr,
		    unsigned long rtt_addr,
		    unsigned long map_addr,
		    unsigned long ulevel,
		    struct smc_result *res)
{
	res->x[0] = rtt_create(rd_addr, rtt_addr, map_addr, ulevel, 0UL, false);
}

void smc_rtt_aux_create(unsigned long rd_addr,
			unsigned long rtt_addr,
			unsigned long map_addr,
			unsigned long ulevel,
			unsigned long index,
			struct smc_result *res)
{
	res->x[0] = rtt_create(rd_addr, rtt_addr, map_addr, ulevel, index, true);
}

/*
 * Helper function to verify if an IPA is aux-referenced or not.
 */
static bool ipa_is_aux_ref(struct rd *rd, unsigned long ipa)
{
	/*
	 * Perform a table walk for each aux table to see if it is referenced
	 * by its Root Translation Table and hence, if it is auxiliaary-referenced.
	 *
	 * @TODO: If RMM maintains a refcount for aux reference, this iteration
	 *	  can be avoided.
	 */
	for (unsigned int i = 0U; i < rd->num_aux_planes; i++) {
		struct s2tt_context *aux_ctx = &rd->s2_ctx[i + 1U];
		struct s2tt_walk aux_walk;
		unsigned long *aux_s2tt, aux_s2tte;

		granule_lock(aux_ctx->g_rtt, GRANULE_STATE_RTT);

		s2tt_walk_lock_unlock(aux_ctx, ipa,
				      aux_ctx->s2_starting_level, &aux_walk);
		aux_s2tt = buffer_granule_mecid_map(aux_walk.g_llt, SLOT_RTT2, aux_ctx->mecid);

		assert(aux_s2tt != NULL);

		aux_s2tte = s2tte_read(&aux_s2tt[aux_walk.index]);
		buffer_unmap(aux_s2tt);
		granule_unlock(aux_walk.g_llt);

		if (!s2tte_is_unassigned_ns(UNUSED_PTR, aux_s2tte)) {
			/* Return the level of the parent table */
			return true;
		}
	}

	return false;
}

/*
 * Fold a child RTT into its parent and report the RMI result through @res.
 * The locked parent pins the child granule through acquisition; a pending
 * tracking transition cannot invalidate this owned RTT reference.
 */
static void rtt_fold(unsigned long rd_addr,
		     unsigned long map_addr,
		     unsigned long ulevel,
		     unsigned long s2tt_index,
		     bool aux,
		     struct smc_result *res)
{
	struct granule *g_rd;
	struct granule *g_tbl;
	struct rd *rd;
	struct s2tt_walk wi;
	unsigned long *table, *parent_s2tt, parent_s2tte;
	long level = (long)ulevel;
	unsigned long rtt_addr;
	unsigned long ret;
	unsigned long s2tte;
	struct s2tt_context *s2_ctx;
	bool in_par;
	tlb_handler_t tlb_handler;
	tlb_handler_per_vmids_t tlb_handler_per_vmids;
	unsigned int rtt_err_code = (aux ? RMI_ERROR_RTT_AUX : RMI_ERROR_RTT);

	ret = tr_find_lock_granule(rd_addr, GRANULE_SIZE,
				   GRANULE_STATE_RD, &g_rd);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	in_par = addr_in_par(rd, map_addr);

	if (!validate_rtt_structure_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (aux) {
		if (!validate_aux_rtt_args(rd, s2tt_index, map_addr)) {
			buffer_unmap(rd);
			granule_unlock(g_rd);
			res->x[0] = RMI_ERROR_INPUT;
			res->x[2] = 0UL;
			return;
		}
		s2_ctx = &rd->s2_ctx[s2tt_index];
	} else {
		s2_ctx = &rd->s2_ctx[PRIMARY_S2_CTX_ID];
	}

	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	s2tt_walk_lock_unlock(s2_ctx, map_addr, level - 1L, &wi);
	if (wi.last_level < (level - 1L)) {
		ret = pack_return_code_level(rtt_err_code, (unsigned char)wi.last_level);
		goto out_unlock_parent_table;
	}

	parent_s2tt = buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx->mecid);
	assert(parent_s2tt != NULL);

	parent_s2tte = s2tte_read(&parent_s2tt[wi.index]);
	if (!s2tte_is_table(s2_ctx, parent_s2tte, level - 1L)) {
		ret = pack_return_code_level(rtt_err_code, (unsigned char)(level - 1L));
		goto out_unmap_parent_table;
	}

	/*
	 * For an unprotected IPA and a level other than the start level,
	 * verify that the Primary RTT entry of the IPA is not
	 * auxiliary-referenced.
	 */
	if (!aux && !in_par && rd->rtt_tree_pp && (level > s2_ctx->s2_starting_level)) {
		if (ipa_is_aux_ref(rd, map_addr)) {
			/* Return the level of the parent table */
			ret = pack_return_code_level(RMI_ERROR_RTT,
					(unsigned char)wi.last_level);
			goto out_unmap_parent_table;
		}
	}

	rtt_addr = s2tte_pa(s2_ctx, parent_s2tte, level - 1L);
	g_tbl = tr_addr_to_granule(rtt_addr);
	granule_lock(g_tbl, GRANULE_STATE_RTT);

	table = buffer_granule_mecid_map(g_tbl, SLOT_RTT2, s2_ctx->mecid);
	assert(table != NULL);

	s2tte = s2tte_read(&table[0U]);

	/*
	 * The command can succeed only if all 512 S2TTEs are of the same type.
	 * We first check the table's ref. counter to speed up the case when
	 * the host makes a guess whether a memory region can be folded.
	 */
	if (granule_refcount_read(g_tbl) == 0U) {
		if (s2tt_is_unassigned_destroyed_block(s2_ctx, table, s2tte)) {
			parent_s2tte = s2tte_create_unassigned_destroyed(s2_ctx, s2tte);
		} else if (s2tt_is_unassigned_empty_block(s2_ctx, table, s2tte)) {
			parent_s2tte = s2tte_create_unassigned_empty(s2_ctx, s2tte);
		} else if (s2tt_is_unassigned_ram_block(s2_ctx, table, s2tte)) {
			parent_s2tte = s2tte_create_unassigned_ram(s2_ctx, s2tte);
		} else if (s2tt_is_unassigned_ns_block(s2_ctx, table, s2tte)) {
			parent_s2tte = s2tte_create_unassigned_ns(s2_ctx, UNUSED_UL);
		} else if (s2tt_maps_assigned_ns_block(s2_ctx, table, level, s2tte)) {
			/*
			 * The RMM specification does not allow creating block entries less than
			 * S2TT_MIN_BLOCK_LEVEL for ASSIGNED_NS state.
			 */
			if (level <= S2TT_MIN_BLOCK_LEVEL) {
				ret = pack_return_code_level(RMI_ERROR_RTT,
						(unsigned char)wi.last_level);
				goto out_unmap_table;
			}

			/*
			 * Since s2tt_maps_assigned_ns_block() has succedded,
			 * the PA in first entry of the table is aligned at
			 * parent level. Use the TTE from the first entry
			 * directly as it also has the NS attributes to be used
			 * for the parent block entry.
			 */
			parent_s2tte = s2tte_create_assigned_ns(s2_ctx, s2tte,
								level - 1L, UNUSED_UL);
		} else {
			/*
			 * The table holds a mixture of destroyed and
			 * unassigned entries.
			 */
			ret = pack_return_code_level(rtt_err_code, (unsigned char)level);
			goto out_unmap_table;
		}
		atomic_granule_put(wi.g_llt);
	} else if (granule_refcount_read(g_tbl) ==
					(unsigned short)S2TTES_PER_S2TT) {

		unsigned long block_pa;

		/*
		 * The RMM specification does not allow creating block
		 * entries less than S2TT_MIN_BLOCK_LEVEL even though
		 * permitted by the Arm Architecture.
		 * Hence ensure that the table being folded is at a level
		 * higher than the S2TT_MIN_BLOCK_LEVEL.
		 *
		 * A fully populated table cannot be destroyed if that
		 * would create a block mapping below S2TT_MIN_BLOCK_LEVEL.
		 */
		if (level <= S2TT_MIN_BLOCK_LEVEL) {
			ret = pack_return_code_level(RMI_ERROR_RTT,
						(unsigned char)wi.last_level);
			goto out_unmap_table;
		}

		block_pa = s2tte_pa(s2_ctx, s2tte, level);

		/*
		 * The table must also refer to a contiguous block through the
		 * same type of s2tte, either Assigned or Valid.
		 */
		if (s2tt_maps_assigned_empty_block(s2_ctx, table, level, s2tte)) {
			parent_s2tte = s2tte_create_assigned_empty(s2_ctx,
					block_pa, level - 1L, s2tte);
		} else if (s2tt_maps_assigned_ram_block(s2_ctx,
							table, level,
							s2tte)) {
			parent_s2tte = s2tte_create_assigned_ram(s2_ctx,
								 block_pa,
								 level - 1L,
								 s2tte);
		} else if (s2tt_maps_assigned_destroyed_block(s2_ctx,
							      table, level,
							      s2tte)) {
			parent_s2tte = s2tte_create_assigned_destroyed(s2_ctx,
							block_pa, level - 1L,
							s2tte);
		} else if (s2tt_maps_assigned_dev_empty_block(s2_ctx,
								table, level,
								s2tte)) {
			parent_s2tte = s2tte_create_assigned_dev_empty(s2_ctx,
									block_pa,
									level - 1L,
									s2tte);
		} else if (s2tt_maps_assigned_dev_destroyed_block(s2_ctx,
								  table, level,
								  s2tte)) {
			parent_s2tte = s2tte_create_assigned_dev_destroyed(s2_ctx,
									   block_pa,
									   level - 1L,
									   s2tte);
		} else if (s2tt_maps_assigned_dev_dev_block(s2_ctx, table, level,
							    s2tte)) {
			parent_s2tte = s2tte_create_assigned_dev_dev(s2_ctx,
									s2tte,
									level - 1L,
									s2tte);
		/* The table contains mixed entries that cannot be folded */
		} else {
			ret = pack_return_code_level(rtt_err_code, (unsigned char)level);
			goto out_unmap_table;
		}

		granule_refcount_dec(g_tbl, (unsigned short)S2TTES_PER_S2TT);
	} else {
		/*
		 * The table holds a mixture of different types of s2ttes.
		 */
		ret = pack_return_code_level(rtt_err_code, (unsigned char)level);
		goto out_unmap_table;
	}

	/*
	 * Break before make.
	 */
	s2tte_write(&parent_s2tt[wi.index], 0UL);

	if (s2tte_is_assigned_ram(s2_ctx, parent_s2tte, level - 1L) ||
	    s2tte_is_assigned_ns(s2_ctx, parent_s2tte, level - 1L)  ||
	    s2tte_is_assigned_dev_dev(s2_ctx, parent_s2tte, level - 1L)) {
		tlb_handler = invalidate_pages_in_block;
		tlb_handler_per_vmids = invalidate_pages_in_block_for_contexts;
	} else {
		tlb_handler = invalidate_page_block;
		tlb_handler_per_vmids = invalidate_page_block_per_vmids;
	}

	if (s2_ctx->indirect_s2ap) {
		assert(!rd->rtt_tree_pp);

		/* Invalidate TLBs for all Plane VMIDs */
		tlb_handler_per_vmids(rd, map_addr, level);
	} else {
		tlb_handler(s2_ctx, rd, map_addr, level);
	}

	ret = RMI_SUCCESS;
	res->x[1] = rtt_addr;

	s2tte_write(&parent_s2tt[wi.index], parent_s2tte);

	buffer_unmap(table);
	granule_unlock_transition_to_delegated(g_tbl);
	goto out_unmap_parent_table;

out_unmap_table:
	buffer_unmap(table);
	granule_unlock(g_tbl);
out_unmap_parent_table:
	buffer_unmap(parent_s2tt);
out_unlock_parent_table:
	buffer_unmap(rd);
	granule_unlock(g_rd);
	granule_unlock(wi.g_llt);
	res->x[0] = ret;
}

void smc_rtt_fold(unsigned long rd_addr,
		  unsigned long map_addr,
		  unsigned long ulevel,
		  struct smc_result *res)
{
	rtt_fold(rd_addr, map_addr, ulevel, 0UL, false, res);
}

void smc_rtt_aux_fold(unsigned long rd_addr,
		      unsigned long map_addr,
		      unsigned long ulevel,
		      unsigned long index,
		      struct smc_result *res)
{
	rtt_fold(rd_addr, map_addr, ulevel, index, true, res);
}

/*
 * Remove an unused child RTT and report the RMI result through @res.
 * The locked parent pins the child granule through acquisition; a pending
 * tracking transition cannot invalidate this owned RTT reference.
 */
static void rtt_destroy(unsigned long rd_addr,
			unsigned long map_addr,
			unsigned long ulevel,
			unsigned long index,
			bool aux,
			struct smc_result *res)
{
	struct granule *g_rd;
	struct granule *g_tbl;
	struct rd *rd;
	struct s2tt_walk wi;
	unsigned long *parent_s2tt, parent_s2tte;
	long level = (long)ulevel;
	unsigned long  rtt_addr;
	unsigned long ret;
	struct s2tt_context *s2_ctx;
	bool in_par, skip_non_live = false;
	tlb_handler_t tlb_handler;
	tlb_handler_per_vmids_t tlb_handler_per_vmids;
	unsigned int rtt_err_code = (aux ? RMI_ERROR_RTT_AUX : RMI_ERROR_RTT);

	ret = tr_find_lock_granule(rd_addr, GRANULE_SIZE,
				   GRANULE_STATE_RD, &g_rd);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		res->x[2] = 0UL;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	in_par = addr_in_par(rd, map_addr);

	if (!validate_rtt_structure_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		res->x[2] = 0UL;
		return;
	}

	if (aux) {
		if (!validate_aux_rtt_args(rd, index, map_addr)) {
			buffer_unmap(rd);
			granule_unlock(g_rd);
			res->x[0] = RMI_ERROR_INPUT;
			res->x[2] = 0UL;
			return;
		}
		s2_ctx = &rd->s2_ctx[index];
	} else {
		s2_ctx = &rd->s2_ctx[PRIMARY_S2_CTX_ID];
	}

	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	s2tt_walk_lock_unlock(s2_ctx, map_addr, level - 1L, &wi);

	parent_s2tt = buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx->mecid);
	assert(parent_s2tt != NULL);

	parent_s2tte = s2tte_read(&parent_s2tt[wi.index]);

	if ((wi.last_level < (level - 1L)) ||
	    !s2tte_is_table(s2_ctx, parent_s2tte, level - 1L)) {
		ret = pack_return_code_level(rtt_err_code, (unsigned char)wi.last_level);
		skip_non_live = true;
		goto out_unmap_parent_table;
	}

	rtt_addr = s2tte_pa(s2_ctx, parent_s2tte, level - 1L);

	/*
	 * The locked parent keeps this child in RTT state and its metadata alive.
	 * Acquire it directly without a new tracking lookup.
	 */
	g_tbl = tr_addr_to_granule(rtt_addr);
	granule_lock(g_tbl, GRANULE_STATE_RTT);

	/*
	 * Read the refcount value. RTT granule is always accessed locked, thus
	 * the refcount can be accessed without atomic operations.
	 */
	if (granule_refcount_read(g_tbl) != 0U) {
		ret = pack_return_code_level(rtt_err_code, (unsigned char)level);
		granule_unlock(g_tbl);
		goto out_unmap_parent_table;
	}

	/*
	 * For an unprotected IPA and a level other than the start level,
	 * verify that the Primary RTT entry of the IPA is not
	 * auxiliary-referenced.
	 */
	if (!aux && !in_par && rd->rtt_tree_pp && (level > s2_ctx->s2_starting_level)) {
		if (ipa_is_aux_ref(rd, map_addr)) {
			/* Return the level of the parent table */
			ret = pack_return_code_level(RMI_ERROR_RTT,
					(unsigned char)wi.last_level);
			granule_unlock(g_tbl);
			goto out_unmap_parent_table;
		}
	}

	if (in_par) {
		/*
		 * On a transition from any RIPAS to DESTROYED, the Access
		 * Permissions need to be reset.
		 */
		parent_s2tte = s2tte_create_unassigned_destroyed(s2_ctx,
							default_protected_ap(s2_ctx));
	} else {
		parent_s2tte = s2tte_create_unassigned_ns(s2_ctx, UNUSED_UL);
	}

	atomic_granule_put(wi.g_llt);

	/*
	 * Break before make. Note that this may cause spurious S2 aborts.
	 */
	s2tte_write(&parent_s2tt[wi.index], 0UL);

	if (in_par) {
		/* For protected IPA, all S2TTEs in the RTT will be invalid */
		tlb_handler = invalidate_page_block;
		tlb_handler_per_vmids = invalidate_page_block_per_vmids;
	} else {
		/*
		 * For unprotected IPA, invalidate the TLB for the entire range
		 * mapped by the RTT as it may have valid NS mappings.
		 */
		tlb_handler = invalidate_pages_in_block;
		tlb_handler_per_vmids = invalidate_pages_in_block_for_contexts;
	}

	if (s2_ctx->indirect_s2ap) {
		assert(!rd->rtt_tree_pp);

		/* Invalidate TLBs for all Plane VMIDs */
		tlb_handler_per_vmids(rd, map_addr, level);
	} else {
		tlb_handler(s2_ctx, rd, map_addr, level);
	}

	s2tte_write(&parent_s2tt[wi.index], parent_s2tte);

	granule_unlock_transition_to_delegated(g_tbl);

	ret = RMI_SUCCESS;
	res->x[1] = rtt_addr;
	skip_non_live = true;

out_unmap_parent_table:
	if (skip_non_live) {
		res->x[2] = s2tt_skip_non_live_entries(s2_ctx, map_addr,
						       parent_s2tt, &wi);
	} else {
		res->x[2] = map_addr;
	}

	buffer_unmap(parent_s2tt);
	granule_unlock(wi.g_llt);
	buffer_unmap(rd);
	granule_unlock(g_rd);
	res->x[0] = ret;
}

void smc_rtt_destroy(unsigned long rd_addr,
		     unsigned long map_addr,
		     unsigned long ulevel,
		     struct smc_result *res)
{
	rtt_destroy(rd_addr, map_addr, ulevel, 0UL, false, res);
}

void smc_rtt_aux_destroy(unsigned long rd_addr,
			 unsigned long map_addr,
			 unsigned long ulevel,
			 unsigned long index,
			 struct smc_result *res)
{
	rtt_destroy(rd_addr, map_addr, ulevel, index, true, res);
}

/*
 * We don't hold a reference on the NS granule when it is
 * mapped into a realm. Instead we rely on the guarantees
 * provided by the architecture to ensure that a NS access
 * to a protected granule is prohibited even within the realm.
 */
/*
 * We don't hold a reference on the NS granule when it is
 * mapped into a realm. Instead we rely on the guarantees
 * provided by the architecture to ensure that a NS access
 * to a protected granule is prohibited even within the realm.
 */
void smc_rtt_read_entry(unsigned long rd_addr,
			unsigned long map_addr,
			unsigned long ulevel,
			struct smc_result *res)
{
	struct granule *g_rd;
	struct rd *rd;
	struct s2tt_walk wi;
	unsigned long *s2tt, s2tte;
	unsigned long ret;
	long level = (long)ulevel;
	struct s2tt_context s2_ctx;

	ret = tr_find_lock_granule(rd_addr, GRANULE_SIZE,
				   GRANULE_STATE_RD, &g_rd);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_rtt_entry_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	s2_ctx = rd->s2_ctx[PRIMARY_S2_CTX_ID];
	buffer_unmap(rd);

	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);
	granule_unlock(g_rd);

	s2tt_walk_lock_unlock(&s2_ctx, map_addr, level, &wi);
	s2tt = buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx.mecid);
	assert(s2tt != NULL);

	s2tte = s2tte_read(&s2tt[wi.index]);
	res->x[1] = (unsigned long)wi.last_level;

	if (s2tte_is_unassigned_empty(&s2_ctx, s2tte)) {
		res->x[2] = RMI_UNASSIGNED;
		res->x[3] = 0UL;
		res->x[4] = (unsigned long)RIPAS_EMPTY;
	} else if (s2tte_is_unassigned_ram(&s2_ctx, s2tte)) {
		res->x[2] = RMI_UNASSIGNED;
		res->x[3] = 0UL;
		res->x[4] = (unsigned long)RIPAS_RAM;
	} else if (s2tte_is_unassigned_destroyed(&s2_ctx, s2tte)) {
		res->x[2] = RMI_UNASSIGNED;
		res->x[3] = 0UL;
		res->x[4] = (unsigned long)RIPAS_DESTROYED;
	} else if (s2tte_is_assigned_empty(&s2_ctx, s2tte, wi.last_level)) {
		res->x[2] = RMI_ASSIGNED;
		res->x[3] = s2tte_pa(&s2_ctx, s2tte, wi.last_level);
		res->x[4] = (unsigned long)RIPAS_EMPTY;
	} else if (s2tte_is_assigned_ram(&s2_ctx, s2tte, wi.last_level)) {
		res->x[2] = RMI_ASSIGNED;
		res->x[3] = s2tte_pa(&s2_ctx, s2tte, wi.last_level);
		res->x[4] = (unsigned long)RIPAS_RAM;
	} else if (s2tte_is_assigned_destroyed(&s2_ctx, s2tte, wi.last_level)) {
		res->x[2] = RMI_ASSIGNED;
		res->x[3] = s2tte_pa(&s2_ctx, s2tte, wi.last_level);
		res->x[4] = (unsigned long)RIPAS_DESTROYED;
	} else if (s2tte_is_assigned_dev_empty(&s2_ctx, s2tte, wi.last_level)) {
		res->x[2] = RMI_ASSIGNED_DEV;
		res->x[3] = s2tte_pa(&s2_ctx, s2tte, wi.last_level);
		res->x[4] = (unsigned long)RIPAS_EMPTY;
	} else if (s2tte_is_assigned_dev_destroyed(&s2_ctx, s2tte,
							wi.last_level)) {
		res->x[2] = RMI_ASSIGNED_DEV;
		res->x[3] = s2tte_pa(&s2_ctx, s2tte, wi.last_level);
		res->x[4] = (unsigned long)RIPAS_DESTROYED;
	} else if (s2tte_is_assigned_dev_dev(&s2_ctx, s2tte, wi.last_level)) {
		res->x[2] = RMI_ASSIGNED_DEV;
		res->x[3] = s2tte_pa(&s2_ctx, s2tte, wi.last_level);
		res->x[4] = (unsigned long)RIPAS_DEV;
	} else if (s2tte_is_unassigned_ns(&s2_ctx, s2tte)) {
		res->x[2] = RMI_UNASSIGNED;
		res->x[3] = 0UL;
		res->x[4] = (unsigned long)RIPAS_EMPTY;
	} else if (s2tte_is_assigned_ns(&s2_ctx, s2tte, wi.last_level)) {
		res->x[2] = RMI_ASSIGNED;
		res->x[3] = host_ns_s2tte(&s2_ctx, s2tte, wi.last_level);
		res->x[4] = (unsigned long)RIPAS_EMPTY;
	} else if (s2tte_is_table(&s2_ctx, s2tte, wi.last_level)) {
		res->x[2] = RMI_TABLE;
		res->x[3] = s2tte_pa(&s2_ctx, s2tte, wi.last_level);
		res->x[4] = (unsigned long)RIPAS_EMPTY;
	} else {
		assert(false);
	}

	buffer_unmap(s2tt);
	granule_unlock(wi.g_llt);

	res->x[0] = RMI_SUCCESS;
}

/*
 * Update the ripas value for the entry pointed by @s2ttep.
 *
 * Returns:
 *  < 0  - On error and the operation was aborted,
 *	   e.g., entry cannot have a ripas.
 *    0  - Operation was success and no TLBI is required.
 *  > 0  - Operation was success and TLBI is required.
 * Sets:
 * @(*do_tlbi) to 'true' if the TLBs have to be invalidated.
 */
static int update_ripas(struct s2tt_context *s2_ctx,
			unsigned long *s2ttep, long level,
			enum ripas ripas_val,
			enum ripas_change_destroyed change_destroyed)
{
	unsigned long pa, s2tte = s2tte_read(s2ttep);
	int ret = 0;

	assert(s2_ctx != NULL);

	if (!s2tte_has_ripas(s2_ctx, s2tte, level)) {
		return -EPERM;
	}

	/*
	 * A drain-pending marker means an in-flight SRO still owns this
	 * architecturally invalid slot. The owner may be preparing a new
	 * live mapping or completing deferred maintenance for the previous
	 * OA. Block the RIPAS transition (in particular DESTROYED -> RAM,
	 * which the realm can request via RSI_IPA_STATE_SET) until the SRO
	 * completes and clears the marker.
	 */
	if (s2tte_drain_pending(s2tte)) {
		return -EAGAIN;
	}

	if (ripas_val == RIPAS_RAM) {
		if (s2tte_is_unassigned_empty(s2_ctx, s2tte)) {
			s2tte = s2tte_create_unassigned_ram(s2_ctx, s2tte);
		} else if (s2tte_is_unassigned_destroyed(s2_ctx, s2tte)) {
			if (change_destroyed == CHANGE_DESTROYED) {
				s2tte = s2tte_create_unassigned_ram(s2_ctx, s2tte);
			} else {
				return -EINVAL;
			}
		} else if (s2tte_is_assigned_empty(s2_ctx, s2tte, level)) {
			pa = s2tte_pa(s2_ctx, s2tte, level);
			s2tte = s2tte_create_assigned_ram(s2_ctx, pa, level, s2tte);
		} else if (s2tte_is_assigned_destroyed(s2_ctx, s2tte, level)) {
			if (change_destroyed == CHANGE_DESTROYED) {
				pa = s2tte_pa(s2_ctx, s2tte, level);
				s2tte = s2tte_create_assigned_ram(s2_ctx, pa,
					level, s2tte);
			} else {
				return -EINVAL;
			}
		} else if (s2tte_is_assigned_dev_empty(s2_ctx, s2tte, level) ||
			   s2tte_is_assigned_dev_destroyed(s2_ctx, s2tte, level) ||
			   s2tte_is_assigned_dev_dev(s2_ctx, s2tte, level)) {
			return -EINVAL;
		} else {
			/* No action is required */
			return 0;
		}
	} else if (ripas_val == RIPAS_EMPTY) {
		if (s2tte_is_unassigned_ram(s2_ctx, s2tte) ||
		    s2tte_is_unassigned_destroyed(s2_ctx, s2tte)) {
			s2tte = s2tte_create_unassigned_empty(s2_ctx, s2tte);
		} else if (s2tte_is_assigned_ram(s2_ctx, s2tte, level) ||
			   s2tte_is_assigned_destroyed(s2_ctx, s2tte, level)) {
			pa = s2tte_pa(s2_ctx, s2tte, level);
			s2tte = s2tte_create_assigned_empty(s2_ctx, pa, level,
							    s2tte);
			/* TLBI is required */
			ret = 1;
		} else if (s2tte_is_assigned_dev_dev(s2_ctx, s2tte, level) ||
			   s2tte_is_assigned_dev_destroyed(s2_ctx, s2tte, level)) {
			pa = s2tte_pa(s2_ctx, s2tte, level);
			s2tte = s2tte_create_assigned_dev_empty(s2_ctx, pa,
								level, s2tte);
			/* TLBI is required */
			ret = 1;
		} else {
			/* No action is required */
			return 0;
		}
	} else {
		assert(false);
	}

	s2tte_write(s2ttep, s2tte);
	return ret;
}

void smc_rtt_init_ripas(unsigned long rd_addr,
			unsigned long base,
			unsigned long top,
			struct smc_result *res)
{
	struct granule *g_rd;
	struct rd *rd;
	unsigned long addr, map_size;
	struct s2tt_walk wi;
	struct s2tt_context *s2_ctx;
	unsigned long s2tte, *s2tt;
	long level;
	unsigned long index;
	unsigned long ret;
	unsigned int s2ttes_per_s2tt;

	if (top <= base) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	ret = tr_find_lock_granule(rd_addr, GRANULE_SIZE,
				   GRANULE_STATE_RD, &g_rd);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_map_addr(base, S2TT_PAGE_LEVEL, rd) ||
	    !validate_map_addr(top, S2TT_PAGE_LEVEL, rd) ||
	    !addr_in_par(rd, base) || !addr_in_par(rd, top - GRANULE_SIZE)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (get_rd_state_locked(rd) != REALM_NEW) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_REALM;
		return;
	}

	s2_ctx = &rd->s2_ctx[PRIMARY_S2_CTX_ID];
	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	s2tt_walk_lock_unlock(s2_ctx, base, S2TT_PAGE_LEVEL, &wi);
	level = wi.last_level;
	s2tt = buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx->mecid);
	assert(s2tt != NULL);

	map_size = s2tte_map_size(level);
	addr = base & ~(map_size - 1UL);

	/*
	 * If the RTTE covers a range below "base", we need to go deeper.
	 */
	if (addr != base) {
		res->x[0] = pack_return_code_level(RMI_ERROR_RTT,
						(unsigned char)level);
		goto out_unmap_llt;
	}

	s2ttes_per_s2tt =
		(unsigned int)((level == S2TT_MIN_STARTING_LEVEL_LPA2) ?
			S2TTES_PER_S2TT_LM1 : S2TTES_PER_S2TT);
	for (index = wi.index; index < s2ttes_per_s2tt; index++) {
		unsigned long next = addr + map_size;

		/*
		 * Break on "top_align" failure condition,
		 * or if this entry crosses the range.
		 */
		if (next > top) {
			break;
		}

		s2tte = s2tte_read(&s2tt[index]);
		if (s2tte_is_unassigned_empty(s2_ctx, s2tte)) {
			s2tte = s2tte_create_unassigned_ram(s2_ctx, s2tte);
			s2tte_write(&s2tt[index], s2tte);
		} else if (s2tte_is_assigned_empty(s2_ctx, s2tte, level)) {
			unsigned long pa = s2tte_pa(s2_ctx, s2tte, level);
			s2tte = s2tte_create_assigned_ram(s2_ctx, pa, level, s2tte);
			s2tte_write(&s2tt[index], s2tte);
		} else if (!s2tte_is_assigned_ram(s2_ctx, s2tte, level) &&
			   !s2tte_is_unassigned_ram(s2_ctx, s2tte)) {
			break;
		}
		addr = next;
	}

	if (addr > base) {
		res->x[0] = RMI_SUCCESS;
		res->x[1] = addr;
	} else {
		res->x[0] = pack_return_code_level(RMI_ERROR_RTT,
						(unsigned char)level);
	}

out_unmap_llt:
	buffer_unmap(s2tt);
	buffer_unmap(rd);
	granule_unlock(wi.g_llt);
	granule_unlock(g_rd);
}

/*
 * Returns the memory size starting at pa @s2tte that is NOT mapped in any of
 * the auxiliary RTTs. This function makes use of the refcount of the granules
 * to ensure that there is no mapping in the auxiliary RTTs.
 *
 * Fine DATA states prevent tracking transition claims during validation.
 * TODO: Auxiliary RTT callers must retain a coarse descriptor lock across
 * validation and handle pending transitions through the tracking APIs. A live
 * coarse mapping alone does not prevent a split from blocking a new lookup.
 *
 * Note that:
 *	- @s2tte is a valid (page or block) descriptor in the primary RTT tree.
 *	- The RTT where @s2tte resides is locked.
 */
unsigned long not_aux_mappings(struct s2tt_context *s2_ctx,
			       unsigned long s2tte, long level)
{
	unsigned long map_size = s2tte_map_size((int)level);
	unsigned long data_addr = s2tte_pa(s2_ctx, s2tte, level);
	unsigned long offset = 0UL;

	while (offset < map_size) {
		/*
		 * The locked leaf RTT orders this DATA lookup. Locking the active
		 * granule also stabilizes a possible coarse-to-fine tracking
		 * transition while its refcount is inspected.
		 */
		struct granule *g_data;
		unsigned long tracking_size;
		unsigned long ret __unused;

		ret = tr_find_lock_active_granule(data_addr + offset, GRANULE_STATE_DATA,
						  &g_data, &tracking_size);
		assert(ret == RMI_SUCCESS);
		assert(tracking_size <= (map_size - offset));

		if (granule_refcount_read_acquire(g_data) > 0U) {
			granule_unlock(g_data);
			break;
		}
		granule_unlock(g_data);
		offset += tracking_size;
	}

	return offset;
}

/*
 * Update RIPAS in the locked leaf @wi->g_llt over [@base, @top), stopping at
 * its boundary or the first incompatible entry. @rd remains locked and mapped;
 * report the RMI status and completed IPA prefix through @res.
 */
static void rtt_set_ripas_range(struct s2tt_context *s2_ctx,
				unsigned long *s2tt,
				unsigned long base,
				unsigned long top,
				struct s2tt_walk *wi,
				bool rtt_tree_pp,
				enum ripas ripas_val,
				enum ripas_change_destroyed change_destroyed,
				struct smc_result *res,
				struct rd *rd)
{
	unsigned long index;
	long level = wi->last_level;
	unsigned long map_size = s2tte_map_size((int)level);
	unsigned long aux_rtt_offset;

	/* Align to the RTT level */
	unsigned long addr = base & ~(map_size - 1UL);

	/* Make sure we don't touch a range below the requested range */
	if (addr != base) {
		res->x[0] = pack_return_code_level(RMI_ERROR_RTT,
						(unsigned char)level);
		return;
	}

	for (index = wi->index; index < S2TTES_PER_S2TT; index++) {
		int ret;

		/*
		 * Break on "top_align" failure condition,
		 * or if this entry crosses the range.
		 */
		if ((addr + map_size) > top) {
			break;
		}

		if (rtt_tree_pp && (ripas_val == RIPAS_EMPTY) &&
		    s2tte_is_assigned_ram(s2_ctx, s2tt[index], level)) {
			/*
			 * Transition from RAM to EMPTY ripas is permitted only
			 * if there is no valid mappings in auxiliary RTT trees.
			 *
			 * Note that only ASSIGNED_RAM entries can have valid
			 * auxiliary mappings.
			 */

			assert(level >= S2TT_MIN_BLOCK_LEVEL);

			aux_rtt_offset = not_aux_mappings(s2_ctx,
							  s2tt[index], level);

			if (aux_rtt_offset < map_size) {
				/*
				 * There are granules mapped on aux tables.
				 * Report that we cannot make further progress
				 * due to them.
				 */
				res->x[0] = RMI_ERROR_RTT_AUX;
				res->x[1] = addr + aux_rtt_offset;
				return;
			}
		}

		ret = update_ripas(s2_ctx, &s2tt[index], level,
					ripas_val, change_destroyed);
		if (ret < 0) {
			break;
		}

		/* Handle TLBI */
		if (ret != 0) {
			if (s2_ctx->indirect_s2ap) {
				assert(!rd->rtt_tree_pp);

				/* Invalidate TLBs for all Plane VMIDs */
				invalidate_page_block_per_vmids(rd, addr, level);
			} else {
				invalidate_page_block(s2_ctx, rd, addr, level);
			}
		}

		addr += map_size;
	}

	if (addr > base) {
		res->x[0] = RMI_SUCCESS;
		res->x[1] = addr;
	} else {
		res->x[0] = pack_return_code_level(RMI_ERROR_RTT,
						(unsigned char)level);
	}
}

void smc_rtt_set_ripas(unsigned long rd_addr,
		       unsigned long rec_addr,
		       unsigned long base,
		       unsigned long top,
		       struct smc_result *res)
{
	struct granule *g_rd, *g_rec;
	struct rec *rec;
	struct rd *rd;
	struct s2tt_walk wi;
	unsigned long *s2tt;
	struct s2tt_context *s2_ctx;
	unsigned long ret;
	enum ripas ripas_val;
	enum ripas_change_destroyed change_destroyed;

	if ((top <= base) || !GRANULE_ALIGNED(top)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	ret = tr_find_lock_two_fine_granules(rd_addr,
				   GRANULE_STATE_RD,
				   &g_rd,
				   rec_addr,
				   GRANULE_STATE_REC,
				   &g_rec);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	if (granule_refcount_read_acquire(g_rec) != 0U) {
		res->x[0] = RMI_ERROR_REC;
		goto out_unlock_rec_rd;
	}

	rec = buffer_granule_map(g_rec, SLOT_REC);
	assert(rec != NULL);

	if (g_rd != rec->realm_info.g_rd) {
		res->x[0] = RMI_ERROR_REC;
		goto out_unmap_rec;
	}

	ripas_val = rec->set_ripas.ripas_val;
	change_destroyed = rec->set_ripas.change_destroyed;

	/*
	 * Return error in case of target region:
	 * - is not the next chunk of requested region
	 * - extends beyond the end of requested region
	 */
	if ((base != rec->set_ripas.addr) || (top > rec->set_ripas.top)) {
		res->x[0] = RMI_ERROR_INPUT;
		goto out_unmap_rec;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	/*
	 * At this point, we know base == rec->set_ripas.addr
	 * and thus must be aligned to GRANULE size.
	 */
	assert(validate_map_addr(base, S2TT_PAGE_LEVEL, rd));

	s2_ctx = &rd->s2_ctx[PRIMARY_S2_CTX_ID];
	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	/* Walk to the deepest level possible */
	s2tt_walk_lock_unlock(s2_ctx, base, S2TT_PAGE_LEVEL, &wi);

	/*
	 * Base has to be aligned to the level at which
	 * it is mapped in RTT.
	 */
	if (!validate_map_addr(base, wi.last_level, rd)) {
		res->x[0] = pack_return_code_level(RMI_ERROR_RTT,
						(unsigned char)wi.last_level);
		goto out_unlock_llt;
	}

	s2tt = buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx->mecid);
	assert(s2tt != NULL);

	rtt_set_ripas_range(s2_ctx, s2tt, base, top, &wi,
			    rd->rtt_tree_pp, ripas_val,
			    change_destroyed, res, rd);

	if (res->x[0] == RMI_SUCCESS) {
		rec->set_ripas.addr = res->x[1];
	}

	buffer_unmap(s2tt);
out_unlock_llt:
	granule_unlock(wi.g_llt);
	buffer_unmap(rd);
out_unmap_rec:
	buffer_unmap(rec);
out_unlock_rec_rd:
	granule_unlock(g_rec);
	granule_unlock(g_rd);
}

void smc_rtt_set_s2ap(unsigned long rd_addr, unsigned long rec_addr,
		      unsigned long base, unsigned long top,
		      struct smc_result *res)
{
	struct granule *g_rd, *g_rec;
	struct rec *rec;
	struct rd *rd;
	struct s2tt_walk wi;
	struct s2tt_context *s2_ctx;
	unsigned long *s2tt;
	unsigned long perm_index, map_size, s2tt_idx, next, s2tte;
	unsigned long ret;

	if ((top <= base) || !(GRANULE_ALIGNED(top))) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	ret = tr_find_lock_two_fine_granules(rd_addr,
				   GRANULE_STATE_RD,
				   &g_rd,
				   rec_addr,
				   GRANULE_STATE_REC,
				   &g_rec);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	/* Check if the REC is running */
	if (granule_refcount_read_acquire(g_rec) != 0U) {
		res->x[0] = RMI_ERROR_REC;
		goto out_unlock_rec_rd;
	}

	rec = buffer_granule_map(g_rec, SLOT_REC);
	assert(rec != NULL);

	/* Confirm the REC owner */
	if (g_rd != rec->realm_info.g_rd) {
		res->x[0] = RMI_ERROR_REC;
		goto out_unmap_rec;
	}

	/*
	 * Return error in case of target region:
	 * - Is not the next chunk of requested region.
	 * - Extends beyond the end of requested region.
	 */
	if ((base != rec->set_s2ap.base) || (top > rec->set_s2ap.top)) {
		res->x[0] = RMI_ERROR_INPUT;
		goto out_unmap_rec;
	}

	perm_index = rec->set_s2ap.index;

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (base > realm_ipa_size(rd)) {
		res->x[0] = RMI_ERROR_INPUT;
		buffer_unmap(rd);
		goto out_unmap_rec;
	}

	if (rd->rtt_tree_pp) {
		s2tt_idx = (rec->set_s2ap.cookie & ~GRANULE_MASK);
	} else {
		s2tt_idx = PRIMARY_S2_CTX_ID;
	}

	assert(s2tt_idx < MAX_S2_CTXS);

	s2_ctx = &rd->s2_ctx[s2tt_idx];
	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	/* Walk to the deepest level possible */
	s2tt_walk_lock_unlock(s2_ctx, base, S2TT_PAGE_LEVEL, &wi);

	if (!s2tte_is_addr_lvl_aligned(s2_ctx, base, wi.last_level)) {
		unsigned int error_id = (s2tt_idx == PLANE_0_ID) ?
					 RMI_ERROR_RTT : RMI_ERROR_RTT_AUX;

		res->x[0] = pack_return_code_level(error_id, (unsigned char)wi.last_level);
		res->x[1] = base;
		res->x[2] = s2tt_idx;
		goto out_unlock_llt;
	}

	map_size = s2tte_map_size(wi.last_level);
	s2tt = buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx->mecid);
	assert(s2tt != NULL);

	/*
	 * Update the entries in the RTT that we have reached by the walk.
	 */
	next = base;
	while ((wi.index < S2TTES_PER_S2TT) && (next < top)) {
		unsigned int base_index;

		if ((next + map_size) > top) {
			/*
			 * The RTT entry covers the IPA space that partially
			 * lays beyond 'top'. We need the next level RTT to
			 * continue the operation
			 */
			unsigned int error_id = (s2tt_idx == PRIMARY_S2_CTX_ID) ?
					RMI_ERROR_RTT : RMI_ERROR_RTT_AUX;

			res->x[0] = pack_return_code_level(error_id,
						(unsigned char)wi.last_level);
			res->x[1] = next;
			res->x[2] = s2tt_idx;
			goto out_unmap_s2tt;
		}

		s2tte = s2tte_read(&s2tt[wi.index]);
		if (s2tte_is_table(s2_ctx, s2tte, wi.last_level)) {
			/*
			 * We need to walk one more level to continue the
			 * operation as we hit a smaller granularity area
			 * and therefore we need a new walk to reach the leaf
			 * table.
			 */
			break;
		}

		/*
		 * If we are using direct Access Permissions we don't have
		 * base permission index to update the protected entry.
		 *
		 * In this case, we infer the base permission based on whether
		 * the S2TTE entry is DEV or not.
		 */
		if (s2_ctx->indirect_s2ap) {
			base_index = (unsigned int)s2tte_get_pi_index(s2_ctx, s2tte);
		} else {
			if (s2tte_is_assigned_dev(s2_ctx, s2tte) ||
			    s2tte_is_assigned_dev_dev(s2_ctx, s2tte, wi.last_level)) {
				base_index = S2TTE_DEV_DEF_BASE_PERM_IDX;
			} else {
				base_index = S2TTE_DEF_BASE_PERM_IDX;
			}
		}

		/* Update the S2AP with the new overlay permission */
		s2tte = s2tte_update_prot_ap(s2_ctx, s2tte, base_index,
					     (unsigned int)perm_index);
		s2tte_write(&s2tt[wi.index], s2tte);

		/* Only invalidate for valid entries */
		if (s2tte_is_assigned_ram(s2_ctx, s2tte, wi.last_level)) {
			if (s2_ctx->indirect_s2ap) {
				/* Invalidate for all Plane VMIDs */
				invalidate_page_block_per_vmids(rd, next, wi.last_level);
			} else {
				invalidate_page_block(s2_ctx, rd, next, wi.last_level);
			}
		}

		wi.index++;
		next += map_size;
	}

	res->x[0] = RMI_SUCCESS;
	res->x[1] = next;

out_unmap_s2tt:
	rec->set_s2ap.base = next;
	buffer_unmap(s2tt);
out_unlock_llt:
	granule_unlock(wi.g_llt);
	buffer_unmap(rd);
out_unmap_rec:
	buffer_unmap(rec);
out_unlock_rec_rd:
	granule_unlock(g_rec);
	granule_unlock(g_rd);
}

/*
 * Calculate the realigned PA mapped @level. The offset is calculated based
 * on the @ipa mapped at @level.
 */
static unsigned long realign_pa(struct s2tt_context *s2_ctx,
				unsigned long pa_base,
				long level,
				unsigned long ipa)
{
	unsigned long offset = ipa -
			(ipa & s2tte_ipa_lvl_mask(level, s2tt_lpa2_enabled(s2_ctx)));

	return pa_base + offset;
}

/*
 * Update the backing-granule refcount for one active tracking unit.
 * @device selects conventional DATA or mapped device memory. The granule
 * remains in its mapping state and is unlocked before return. On success,
 * @tracking_size receives the number of bytes represented by the granule.
 */
static unsigned long rtt_backing_refcount_one(unsigned long addr,
					       unsigned long remaining,
					       bool device,
					       bool increment,
					       unsigned long *tracking_size)
{
	struct granule *g;
	struct dev_granule *g_dev;
	enum dev_coh_type type __unused;
	unsigned long ret;

	assert(tracking_size != NULL);
	if (device) {
		ret = tr_find_lock_active_dev_granule(addr,
						      DEV_GRANULE_STATE_MAPPED,
						      &g_dev, &type,
						      tracking_size);
		if (ret != RMI_SUCCESS) {
			return ret;
		}
		if ((*tracking_size > remaining) ||
		    !ALIGNED(addr, *tracking_size)) {
			dev_granule_unlock(g_dev);
			return pack_return_code_level_addr(
					RMI_ERROR_TRACKING, (unsigned char)0U, addr);
		}
		if (increment) {
			atomic_dev_granule_get(g_dev);
		} else {
			atomic_dev_granule_put(g_dev);
		}
		dev_granule_unlock(g_dev);
		return RMI_SUCCESS;
	}

	ret = tr_find_lock_active_granule(addr, GRANULE_STATE_DATA, &g,
					  tracking_size);
	if (ret != RMI_SUCCESS) {
		return ret;
	}
	if ((*tracking_size > remaining) || !ALIGNED(addr, *tracking_size)) {
		granule_unlock(g);
		return pack_return_code_level_addr(
				RMI_ERROR_TRACKING, (unsigned char)0U, addr);
	}
	if (increment) {
		atomic_granule_get(g);
	} else {
		atomic_granule_put(g);
	}
	granule_unlock(g);
	return RMI_SUCCESS;
}

/*
 * Update every active backing granule in [@addr, @addr + @size). Tracking
 * granularity may be finer than the S2TT block and can therefore change at a
 * tracking-region boundary. An increment failure is rolled back so no partial
 * auxiliary reference remains. A decrement is an internal cleanup path and
 * must describe an existing, tracking-compatible mapping.
 * Return RMI_SUCCESS or the original lookup error after undoing the completed
 * increment prefix. Rollback results are checked only by assertions.
 *
 * TODO: The auxiliary RTT rework must retain coarse granule locks through
 * updates, rollback and unmap, using tracking APIs to handle pending transitions.
 * A pending transition can currently fail cleanup lookups which callers assert
 * succeed.
 */
static unsigned long rtt_backing_refcount_update(unsigned long addr,
						  unsigned long size,
						  bool device,
						  bool increment)
{
	unsigned long rollback = 0UL;
	unsigned long processed = 0UL;
	unsigned long tracking_size;
	unsigned long error;
	unsigned long ret = RMI_SUCCESS;

	assert((size != 0UL) && GRANULE_ALIGNED(addr) &&
	       GRANULE_ALIGNED(size));

	while (processed < size) {
		ret = rtt_backing_refcount_one(addr + processed,
						size - processed,
						device, increment,
						&tracking_size);
		if (ret != RMI_SUCCESS) {
			break;
		}
		processed += tracking_size;
	}

	if ((ret == RMI_SUCCESS) || !increment) {
		return ret;
	}

	error = ret;

	/* Undo every increment completed before the failing tracking unit. */
	while (rollback < processed) {
		unsigned long rollback_ret __unused;

		rollback_ret = rtt_backing_refcount_one(addr + rollback,
						      processed - rollback, device, false,
						      &tracking_size);
		assert(rollback_ret == RMI_SUCCESS);
		rollback += tracking_size;
	}

	return error;
}

void smc_rtt_aux_map_protected(unsigned long rd_addr,
			       unsigned long map_addr,
			       unsigned long index,
			       struct smc_result *res)
{
	struct granule *g_rd;
	struct rd *rd;
	struct s2tt_walk wi;
	unsigned long *s2tt, primary_s2tte, s2tte;
	struct s2tt_context *s2_ctx, *aux_s2_ctx;
	unsigned long primary_ripas, primary_pa, aux_pa;
	unsigned long map_size;
	unsigned long ret;
	long primary_level;
	enum ripas s2tte_ripas;
	bool device;

	ret = tr_find_lock_granule(rd_addr, GRANULE_SIZE,
				   GRANULE_STATE_RD, &g_rd);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if ((get_rd_state_locked(rd) != REALM_NEW) &&
	    (get_rd_state_locked(rd) != REALM_ACTIVE)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_REALM;
		return;
	}

	if (!validate_rtt_entry_cmds(map_addr, S2TT_PAGE_LEVEL, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if ((!rd->rtt_tree_pp) ||
	    (index == (unsigned long)PRIMARY_S2_CTX_ID) ||
	    (index >= (unsigned long)realm_num_s2_contexts(rd))) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!addr_in_par(rd, map_addr)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	s2_ctx = &rd->s2_ctx[PRIMARY_S2_CTX_ID];

	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	s2tt_walk_lock_unlock(s2_ctx, map_addr, S2TT_PAGE_LEVEL, &wi);
	s2tt = buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx->mecid);
	assert(s2tt != NULL);

	primary_s2tte = s2tte_read(&s2tt[wi.index]);
	buffer_unmap(s2tt);
	granule_unlock(wi.g_llt);

	primary_level = wi.last_level;
	primary_ripas = (unsigned long)s2tte_get_ripas(s2_ctx, primary_s2tte);

	res->x[4] = 0UL;

	/* If the IPA is not assigned on the primary RTT, report and return */
	if (!s2tte_is_assigned_ram(s2_ctx, primary_s2tte, primary_level) &&
	    !s2tte_is_assigned_dev_dev(s2_ctx, primary_s2tte, primary_level)) {
		unsigned long hipas;

		hipas = (s2tte_is_assigned_dev(s2_ctx, primary_s2tte) ?
			 RMI_ASSIGNED_DEV :
			 (s2tte_is_unassigned(s2_ctx, primary_s2tte) ?
			  RMI_UNASSIGNED : RMI_ASSIGNED));

		res->x[0] = pack_return_code_level(RMI_ERROR_RTT,
					(unsigned char)primary_level);
		res->x[1] = (unsigned long)PRIMARY_S2_CTX_ID;
		res->x[2] = (unsigned long)primary_level;
		res->x[3] = hipas;
		res->x[4] = primary_ripas;

		buffer_unmap(rd);
		granule_unlock(g_rd);
		return;
	}

	primary_pa = s2tte_pa(s2_ctx, primary_s2tte, primary_level);
	device = s2tte_is_assigned_dev_dev(s2_ctx, primary_s2tte,
					   primary_level);

	/*
	 * We have retrieved all the info we needed from the walk on the
	 * primary table. Prepare a walk on the auxiliary one.
	 */
	aux_s2_ctx = &rd->s2_ctx[index];
	granule_lock(aux_s2_ctx->g_rtt, GRANULE_STATE_RTT);

	s2tt_walk_lock_unlock(aux_s2_ctx, map_addr, S2TT_PAGE_LEVEL, &wi);
	s2tt = buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, aux_s2_ctx->mecid);
	assert(s2tt != NULL);

	s2tte = s2tte_read(&s2tt[wi.index]);

	/* Aux table level cannot be less than the primary one */
	if (wi.last_level < primary_level) {
		unsigned long hipas;

		hipas = (s2tte_is_assigned_dev(aux_s2_ctx, s2tte) ?
			 RMI_ASSIGNED_DEV :
			 (s2tte_is_unassigned(aux_s2_ctx, s2tte) ?
			  RMI_UNASSIGNED : RMI_ASSIGNED));

		res->x[0] = pack_return_code_level(RMI_ERROR_RTT_AUX,
					     (unsigned char)wi.last_level);
		res->x[1] = index;
		res->x[2] = (unsigned long)primary_level;
		res->x[3] = hipas;
		res->x[4] = primary_ripas;

		buffer_unmap(s2tt);
		granule_unlock(wi.g_llt);
		goto exit_unmap_rd;
	}

	/*
	 * Realign the PA on the primary S2TTE to the level in the
	 * auxiliary RTT entry.
	 */
	aux_pa = realign_pa(aux_s2_ctx, primary_pa, wi.last_level, map_addr);

	s2tte_ripas = s2tte_get_ripas(aux_s2_ctx, s2tte);

	/* If the entry ripas is destroyed, report it and exit */
	if (s2tte_ripas == RIPAS_DESTROYED) {
		res->x[0] = pack_return_code_level(RMI_ERROR_RTT_AUX,
				     (unsigned char)wi.last_level);
		res->x[1] = wi.index;
		res->x[2] = (unsigned long)primary_level;
		res->x[3] = RMI_AUX_DESTROYED;
		res->x[4] = primary_ripas;

		buffer_unmap(s2tt);
		granule_unlock(wi.g_llt);
		goto exit_unmap_rd;
	}

	/*
	 * If the TTE is assigned RAM or Dev DEV, we exit with
	 * success condition.
	 */
	if ((s2tte_is_assigned_ram(aux_s2_ctx, s2tte, wi.last_level)) ||
	    (s2tte_is_assigned_dev_dev(aux_s2_ctx, s2tte, wi.last_level))) {
		res->x[0] = RMI_SUCCESS;

		buffer_unmap(s2tt);
		granule_unlock(wi.g_llt);
		goto exit_unmap_rd;
	}

	/*
	 * Take one reference per active tracking granule. A fine-tracked
	 * range can back a larger S2TT block, whereas a coarse granule
	 * cannot be represented by a smaller block.
	 */
	map_size = s2tte_map_size(wi.last_level);
	ret = rtt_backing_refcount_update(aux_pa, map_size, device, true);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		buffer_unmap(s2tt);
		granule_unlock(wi.g_llt);
		goto exit_unmap_rd;
	}

	if (s2tte_is_assigned_ram(s2_ctx, primary_s2tte, primary_level)) {
		s2tte = s2tte_create_assigned_ram(aux_s2_ctx, aux_pa,
						  wi.last_level, s2tte);
	} else {
		/*
		 * Reset the IPA off the s2tte with the realigned IPA to
		 * create the assigned dev dev mapping.
		 */
		s2tte &= s2tte_to_pa(aux_s2_ctx, UINT64_MAX, S2TT_PAGE_LEVEL);
		s2tte |= pa_to_s2tte(aux_s2_ctx, aux_pa);
		s2tte = s2tte_create_assigned_dev_dev(aux_s2_ctx, aux_pa,
						      wi.last_level, s2tte);
	}

	/* Increment the refcount of the table in the aux tree */
	atomic_granule_get(wi.g_llt);

	s2tte_write(&s2tt[wi.index], s2tte);

	buffer_unmap(s2tt);
	granule_unlock(wi.g_llt);

	res->x[0] = RMI_SUCCESS;

exit_unmap_rd:
	buffer_unmap(rd);
	granule_unlock(g_rd);
}

void smc_rtt_aux_map_unprotected(unsigned long rd_addr,
				 unsigned long map_addr,
				 unsigned long index,
				 struct smc_result *res)
{
	struct granule *g_rd;
	struct rd *rd;
	struct s2tt_walk pri_walk, aux_walk;
	unsigned long *pri_s2tt, *aux_s2tt, pri_s2tte, aux_s2tte;
	struct s2tt_context *s2_ctx, *aux_s2_ctx;
	unsigned long ret;
	long start_level;

	ret = tr_find_lock_granule(rd_addr, GRANULE_SIZE,
				   GRANULE_STATE_RD, &g_rd);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if ((get_rd_state_locked(rd) != REALM_NEW) &&
	    (get_rd_state_locked(rd) != REALM_ACTIVE)) {
		res->x[0] = RMI_ERROR_REALM;
		goto exit_unmap_rd;
	}

	s2_ctx = &rd->s2_ctx[PRIMARY_S2_CTX_ID];
	start_level = s2_ctx->s2_starting_level;

	if (!validate_rtt_entry_cmds(map_addr, start_level, rd) ||
	    addr_in_par(rd, map_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		goto exit_unmap_rd;
	}

	if ((!rd->rtt_tree_pp) ||
	    (index == (unsigned long)PRIMARY_S2_CTX_ID) ||
	    (index >= (unsigned long)realm_num_s2_contexts(rd))) {
		res->x[0] = RMI_ERROR_INPUT;
		goto exit_unmap_rd;
	}

	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	s2tt_walk_lock_unlock(s2_ctx, map_addr, start_level, &pri_walk);
	pri_s2tt = buffer_granule_mecid_map(pri_walk.g_llt, SLOT_RTT, s2_ctx->mecid);
	assert(pri_s2tt != NULL);

	pri_s2tte = s2tte_read(&pri_s2tt[pri_walk.index]);

	buffer_unmap(pri_s2tt);
	granule_unlock(pri_walk.g_llt);

	/* If the IPA is unassigned_ns on the primary RTT, report and return */
	if (s2tte_is_unassigned_ns(s2_ctx, pri_s2tte)) {
		res->x[0] = pack_return_code_level(RMI_ERROR_RTT,
					(unsigned char)pri_walk.last_level);
		goto exit_unmap_rd;
	}

	/* Walk the auxiliary table */
	aux_s2_ctx = &rd->s2_ctx[index];
	granule_lock(aux_s2_ctx->g_rtt, GRANULE_STATE_RTT);

	s2tt_walk_lock_unlock(aux_s2_ctx, map_addr, start_level, &aux_walk);

	/* The auxiliary walk should have stopped at root level */
	assert(aux_walk.last_level == start_level);

	aux_s2tt = buffer_granule_mecid_map(aux_walk.g_llt, SLOT_RTT, aux_s2_ctx->mecid);
	assert(aux_s2tt != NULL);

	aux_s2tte = s2tte_read(&aux_s2tt[aux_walk.index]);

	/* If the entry is already assigned_ns, exit with success condition */
	if (s2tte_is_assigned_ns(aux_s2_ctx, aux_s2tte, aux_walk.last_level)) {
		res->x[0] = RMI_SUCCESS;

		goto exit_unmap_aux_s2tt;
	}

	/*
	 * Copy the entry at root level of the primary tree into the
	 * corresponding entry of the auxiliary tree.
	 */
	s2tte_write(&aux_s2tt[aux_walk.index], pri_s2tte);

	/* Increment the refcount of the parent table in the aux tree */
	atomic_granule_get(aux_walk.g_llt);

	res->x[0] = RMI_SUCCESS;

exit_unmap_aux_s2tt:
	buffer_unmap(aux_s2tt);
	granule_unlock(aux_walk.g_llt);

exit_unmap_rd:
	buffer_unmap(rd);
	granule_unlock(g_rd);
}

/*
 * Remove the protected or device mapping at @unmap_addr from auxiliary RTT
 * @index of Realm @rd_addr. Report the RMI status and, on success or an RTT
 * error, the next IPA through @res. Lock the RD before walking the RTT and
 * keep its leaf locked while dropping backing references and invalidating
 * the translation. Backing-reference cleanup must succeed; its result is
 * checked only in assertion-enabled builds.
 */
void smc_rtt_aux_unmap_protected(unsigned long rd_addr,
				 unsigned long unmap_addr,
				 unsigned long index,
				 struct smc_result *res)
{
	struct granule *g_rd;
	struct rd *rd;
	struct s2tt_walk wi;
	unsigned long *s2tt, s2tte;
	unsigned long pa, map_size;
	unsigned long ret;
	unsigned long refcount_ret __unused;
	struct s2tt_context *s2_ctx;
	bool device;

	ret = tr_find_lock_granule(rd_addr, GRANULE_SIZE,
				   GRANULE_STATE_RD, &g_rd);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_rtt_entry_cmds(unmap_addr, S2TT_PAGE_LEVEL, rd)) {
		res->x[0] = RMI_ERROR_INPUT;
		goto out_unmap_rd;
	}

	if ((!rd->rtt_tree_pp) ||
	    (index == (unsigned long)PRIMARY_S2_CTX_ID) ||
	    (index >= (unsigned long)realm_num_s2_contexts(rd))) {
		res->x[0] = RMI_ERROR_INPUT;
		goto out_unmap_rd;
	}

	if (!addr_in_par(rd, unmap_addr)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	s2_ctx = &rd->s2_ctx[index];

	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	s2tt_walk_lock_unlock(s2_ctx, unmap_addr, S2TT_PAGE_LEVEL, &wi);
	s2tt = buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx->mecid);
	assert(s2tt != NULL);

	s2tte = s2tte_read(&s2tt[wi.index]);

	/* If the IPA is not assigned on the auxiliary RTT, report and return. */
	if (!(s2tte_is_live(s2_ctx, s2tte, wi.last_level) ||
	      s2tte_is_assigned_dev(s2_ctx, s2tte))) {
		res->x[0] = pack_return_code_level(RMI_ERROR_RTT_AUX,
				     (unsigned char)wi.last_level);
		res->x[1] = s2tt_skip_non_live_entries(s2_ctx, unmap_addr,
							s2tt, &wi);
		buffer_unmap(s2tt);
		granule_unlock(wi.g_llt);
		goto out_unmap_rd;
	}

	/*
	 * Save the PA mapped by the entry, as we will need it later to
	 * decrement the reference count for the associated granules.
	 */
	pa = s2tte_pa(s2_ctx, s2tte, wi.last_level);
	device = s2tte_is_assigned_dev_dev(s2_ctx, s2tte, wi.last_level);

	/*
	 * Create the new S2TTE, reusing the original one so that they
	 * have the same Access Permissions.
	 */
	s2tte = s2tte_create_unassigned_empty(s2_ctx, s2tte);

	/* Drop the auxiliary reference from every active backing granule. */
	map_size = s2tte_map_size(wi.last_level);
	refcount_ret = rtt_backing_refcount_update(pa, map_size, device, false);
	assert(refcount_ret == RMI_SUCCESS);

	/* Decrement the refcounter for the table in the aux tree */
	atomic_granule_put(wi.g_llt);

	s2tte_write(&s2tt[wi.index], s2tte);

	if (s2_ctx->indirect_s2ap) {
		/* Invalidate TLBs for all Plane VMIDs */
		invalidate_page_block_per_vmids(rd, unmap_addr, wi.last_level);
	} else {
		invalidate_page_block(s2_ctx, rd, unmap_addr, wi.last_level);
	}

	res->x[0] = RMI_SUCCESS;
	res->x[1] = s2tt_skip_non_live_entries(s2_ctx, unmap_addr, s2tt, &wi);

	buffer_unmap(s2tt);
	granule_unlock(wi.g_llt);

out_unmap_rd:
	buffer_unmap(rd);
	granule_unlock(g_rd);
}

void smc_rtt_aux_unmap_unprotected(unsigned long rd_addr,
				   unsigned long unmap_addr,
				   unsigned long index,
				   struct smc_result *res)
{
	struct granule *g_rd;
	struct rd *rd;
	struct s2tt_walk wi;
	unsigned long *s2tt, s2tte;
	unsigned long ret;
	long start_level;
	struct s2tt_context *s2_ctx;

	ret = tr_find_lock_granule(rd_addr, GRANULE_SIZE,
				   GRANULE_STATE_RD, &g_rd);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if ((!rd->rtt_tree_pp) ||
	    (index == (unsigned long)PRIMARY_S2_CTX_ID) ||
	    (index >= (unsigned long)realm_num_s2_contexts(rd))) {
		res->x[0] = RMI_ERROR_INPUT;
		goto out_unmap_rd;
	}

	s2_ctx = &rd->s2_ctx[index];
	start_level = s2_ctx->s2_starting_level;

	if (!validate_rtt_entry_cmds(unmap_addr, start_level, rd)) {
		res->x[0] = RMI_ERROR_INPUT;
		goto out_unmap_rd;
	}

	if (addr_in_par(rd, unmap_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		goto out_unmap_rd;
	}

	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	/*
	 * Use s2tt_walk_lock_unlock() even for a walk through the starting
	 * level as this API also handles concatenated starting level tables.
	 */
	s2tt_walk_lock_unlock(s2_ctx, unmap_addr, start_level, &wi);
	s2tt = buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx->mecid);
	assert(s2tt != NULL);

	s2tte = s2tte_read(&s2tt[wi.index]);

	if (!s2tte_is_unassigned_ns(s2_ctx, s2tte)) {
		s2tte = s2tte_create_unassigned_ns(UNUSED_PTR, UNUSED_UL);

		s2tte_write(&s2tt[wi.index], s2tte);

		/* Decrement the refcounter for the parent table in the aux tree */
		atomic_granule_put(wi.g_llt);

		if (s2_ctx->indirect_s2ap) {
			/* Invalidate TLBs for all Plane VMIDs */
			invalidate_page_block_per_vmids(rd, unmap_addr, wi.last_level);
		} else {
			invalidate_page_block(s2_ctx, rd, unmap_addr, wi.last_level);
		}
	}

	res->x[0] = RMI_SUCCESS;
	res->x[1] = s2tt_skip_non_live_entries(s2_ctx, unmap_addr, s2tt, &wi);

	buffer_unmap(s2tt);
	granule_unlock(wi.g_llt);

out_unmap_rd:
	buffer_unmap(rd);
	granule_unlock(g_rd);
}

/* Validate one device RTTE and update it with the tracked coherency type. */
static int rtt_dev_mem_set(const struct s2tt_context *s2_ctx,
			   unsigned long *s2ttep, long level,
			   unsigned long dev_mem_pa,
			   enum dev_coh_type type)
{
	unsigned long s2tte;
	int ret = 0;

	s2tte = s2tte_read(s2ttep);
	assert(s2_ctx != NULL);

	if (!s2tte_has_ripas(s2_ctx, s2tte, level)) {
		return -EPERM;
	}

	if (s2tte_is_assigned_dev_empty(s2_ctx, s2tte, level)) {
		unsigned long pa;

		/* Compare the PA with Realm dev_mem_pa */
		pa = s2tte_pa(s2_ctx, s2tte, level);
		if (pa != dev_mem_pa) {
			return -1;
		}

		s2tte = s2tte_create_assigned_dev_dev_coh_type(s2_ctx, s2tte,
							       level, type, s2tte);
	} else {
		return -1;
	}

	s2tte_write(s2ttep, s2tte);
	return ret;
}

/*
 * Validate device RTTEs in [@base, @top) and report range progress.
 *
 * Before updating an entry, validate that its backing PA has an active MAPPED
 * struct dev_granule whose granularity is no larger than the S2TT block. The tracked
 * device type supplies the coherency attribute written into the RTTE.
 */
static void rtt_dev_mem_set_range(struct s2tt_context *s2_ctx,
				  unsigned long *s2tt, unsigned long base,
				  unsigned long top, unsigned long dev_mem_pa,
				  struct s2tt_walk *wi, struct rd *rd,
				  struct smc_result *res)
{
	unsigned long index;
	long level = wi->last_level;
	unsigned long map_size;
	unsigned long addr;

	/* Align to the RTT level */
	map_size = s2tte_map_size((int)level);
	addr = base & ~(map_size - 1UL);
	res->x[0] = pack_return_code_level(RMI_ERROR_RTT,
					   (unsigned char)level);

	/* Make sure we don't touch a range below the requested range */
	if (addr != base) {
		res->x[0] = pack_return_code_level(RMI_ERROR_RTT,
					     (unsigned char)level);
		return;
	}

	for (index = wi->index; index < S2TTES_PER_S2TT; index++) {
		struct dev_granule *g_dev;
		enum dev_coh_type type;
		unsigned long tracking_size;
		unsigned long tr_ret;
		int ret;

		/*
		 * Break on "top_align" failure condition,
		 * or if this entry crosses the range.
		 */
		if ((addr + map_size) > top) {
			break;
		}

		tr_ret = tr_find_lock_active_dev_granule(
					dev_mem_pa, DEV_GRANULE_STATE_MAPPED,
					&g_dev, &type, &tracking_size);
		if (tr_ret != RMI_SUCCESS) {
			if (addr == base) {
				res->x[0] = tr_ret;
			}
			break;
		}

		/* A fine unit may back a block; a coarse unit may not exceed it. */
		if ((tracking_size > map_size) ||
		    !ALIGNED(dev_mem_pa, tracking_size)) {
			dev_granule_unlock(g_dev);
			if (addr == base) {
				res->x[0] = pack_return_code_level_addr(
						RMI_ERROR_TRACKING,
						(unsigned char)0U, dev_mem_pa);
			}
			break;
		}

		ret = rtt_dev_mem_set(s2_ctx, &s2tt[index], level, dev_mem_pa,
					  type);
		dev_granule_unlock(g_dev);
		if (ret < 0) {
			break;
		}

		/* Handle TLBI */
		if (ret != 0) {
			if (s2_ctx->indirect_s2ap) {
				assert(!rd->rtt_tree_pp);

				/* Invalidate TLBs for all Plane VMIDs */
				invalidate_page_block_per_vmids(rd, addr, level);
			} else {
				invalidate_page_block(s2_ctx, rd, addr, level);
			}
		}

		addr += map_size;
		dev_mem_pa += map_size;
	}

	if (addr > base) {
		res->x[0] = RMI_SUCCESS;
		res->x[1] = addr;
	}
}

void smc_rtt_dev_validate(unsigned long rd_addr, unsigned long rec_addr,
			  unsigned long base, unsigned long top,
			  struct smc_result *res)
{
	struct granule *g_rd, *g_rec, *g_vdev;
	struct s2tt_context *s2_ctx;
	unsigned long dev_mem_pa;
	unsigned long *s2tt;
	struct s2tt_walk wi;
	struct vdev *vd;
	struct rec *rec;
	struct rd *rd;
	unsigned long ret;

	if ((top <= base) || !GRANULE_ALIGNED(top)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/* Lock in RD, REC, VDEV, RTT order and retain VDEV through the update. */
	ret = tr_find_lock_two_fine_granules(rd_addr, GRANULE_STATE_RD,
					     &g_rd, rec_addr,
					     GRANULE_STATE_REC, &g_rec);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	/* Ensure REC is not running */
	if (granule_refcount_read_acquire(g_rec) != 0U) {
		res->x[0] = RMI_ERROR_REC;
		goto out_unlock_rec_rd;
	}

	rec = buffer_granule_map(g_rec, SLOT_REC);
	assert(rec != NULL);

	if (g_rd != rec->realm_info.g_rd) {
		res->x[0] = RMI_ERROR_REC;
		goto out_unmap_rec;
	}

	if ((base != rec->dev_mem.addr) || (top > rec->dev_mem.top)) {
		res->x[0] = RMI_ERROR_INPUT;
		goto out_unmap_rec;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	/* Resolve the pending request's VDEV ID through the RD-owned map.
	 * Reject the request if the VDEV is no longer present. */
	if (vdev_find_lock_map(g_rd, rd, rec->vdev_id_1, &g_vdev, &vd) != 0) {
		res->x[0] = RMI_ERROR_INPUT;
		goto out_unmap_rd;
	}

	/* UNLOCK can be pending while the VDEV still appears LOCKED/STARTED. */
	if (((vd->rmi_state != RMI_VDEV_STATE_LOCKED) &&
	     (vd->rmi_state != RMI_VDEV_STATE_STARTED)) ||
	    (vd->comm_state != DEV_COMM_IDLE)) {
		res->x[0] = RMI_ERROR_DEVICE;
		goto out_unmap_vdev;
	}

	/* Compare current VDEV freshness with the nonces saved in the Realm's request.
	 * Reject stale requests after a lock, measurement or interface-report update. */
	if ((vd->attest_info.lock_nonce != rec->vdev_freshness_1.lock_nonce) ||
	    (vd->attest_info.meas_nonce != rec->vdev_freshness_1.meas_nonce) ||
	    (vd->attest_info.report_nonce != rec->vdev_freshness_1.report_nonce)) {
		res->x[0] = RMI_ERROR_DEVICE;
		goto out_unmap_vdev;
	}

	/*
	 * At this point, we know base == rec->dev_mem.addr and thus must be
	 * aligned to GRANULE size.
	 */
	assert(validate_map_addr(base, S2TT_PAGE_LEVEL, rd));

	s2_ctx = plane_to_s2_context(rd, PLANE_0_ID);
	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	/* Walk to the deepest level possible */
	s2tt_walk_lock_unlock(s2_ctx, base, S2TT_PAGE_LEVEL, &wi);

	/* Base has to be aligned to the level at which it is mapped in RTT. */
	if (!validate_map_addr(base, wi.last_level, rd)) {
		res->x[0] = pack_return_code_level(RMI_ERROR_RTT,
					     (unsigned char)wi.last_level);
		goto out_unlock_llt;
	}

	dev_mem_pa = rec->dev_mem.pa;

	s2tt = buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx->mecid);
	assert(s2tt != NULL);

	rtt_dev_mem_set_range(s2_ctx, s2tt, base, top, dev_mem_pa, &wi, rd,
			      res);

	if (res->x[0] == RMI_SUCCESS) {
		rec->dev_mem.addr = res->x[1];
		rec->dev_mem.pa = dev_mem_pa + (res->x[1] - base);
	}

	buffer_unmap(s2tt);
out_unlock_llt:
	granule_unlock(wi.g_llt);

out_unmap_vdev:
	buffer_unmap(vd);
	granule_unlock(g_vdev);

out_unmap_rd:
	buffer_unmap(rd);

out_unmap_rec:
	buffer_unmap(rec);

out_unlock_rec_rd:
	granule_unlock(g_rec);
	granule_unlock(g_rd);
}

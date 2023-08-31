/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <granule.h>
#include <measurement.h>
#include <realm.h>
#include <ripas.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <stddef.h>
#include <string.h>
#include <table.h>

/*
 * Validate the map_addr value passed to RMI_RTT_* and RMI_DATA_* commands.
 */
static bool validate_map_addr(unsigned long map_addr,
			      unsigned long level,
			      struct rd *rd)
{
	return ((map_addr < realm_ipa_size(rd)) &&
		addr_is_level_aligned(map_addr, level));
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

	if ((level < min_level) || (level > RTT_PAGE_LEVEL)) {
		return false;
	}
	return validate_map_addr(map_addr, level, rd);
}

/*
 * Map/Unmap commands can operate up to a level 2 block entry so min_level is
 * the smallest block size.
 */
static bool validate_rtt_map_cmds(unsigned long map_addr,
				  long level,
				  struct rd *rd)
{
	if ((level < RTT_MIN_BLOCK_LEVEL) || (level > RTT_PAGE_LEVEL)) {
		return false;
	}
	return validate_map_addr(map_addr, level, rd);
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
	    (level > RTT_PAGE_LEVEL)) {
		return false;
	}
	return validate_map_addr(map_addr, level, rd);
}

unsigned long smc_rtt_create(unsigned long rd_addr,
			     unsigned long rtt_addr,
			     unsigned long map_addr,
			     unsigned long ulevel)
{
	struct granule *g_rd;
	struct granule *g_tbl;
	struct rd *rd;
	struct granule *g_table_root;
	struct rtt_walk wi;
	unsigned long *s2tt, *parent_s2tt, parent_s2tte;
	long level = (long)ulevel;
	unsigned long ipa_bits;
	unsigned long ret;
	struct realm_s2_context s2_ctx;
	int sl;

	if (!find_lock_two_granules(rtt_addr,
				    GRANULE_STATE_DELEGATED,
				    &g_tbl,
				    rd_addr,
				    GRANULE_STATE_RD,
				    &g_rd)) {
		return RMI_ERROR_INPUT;
	}

	rd = granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_rtt_structure_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		granule_unlock(g_tbl);
		return RMI_ERROR_INPUT;
	}

	g_table_root = rd->s2_ctx.g_rtt;
	sl = realm_rtt_starting_level(rd);
	ipa_bits = realm_ipa_bits(rd);
	s2_ctx = rd->s2_ctx;
	buffer_unmap(rd);

	/*
	 * Lock the RTT root. Enforcing locking order RD->RTT is enough to
	 * ensure deadlock free locking guarentee.
	 */
	granule_lock(g_table_root, GRANULE_STATE_RTT);

	/* Unlock RD after locking RTT Root */
	granule_unlock(g_rd);

	rtt_walk_lock_unlock(g_table_root, sl, ipa_bits,
				map_addr, level - 1L, &wi);
	if (wi.last_level != level - 1L) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned int)wi.last_level);
		goto out_unlock_llt;
	}

	parent_s2tt = granule_map(wi.g_llt, SLOT_RTT);
	assert(parent_s2tt != NULL);

	parent_s2tte = s2tte_read(&parent_s2tt[wi.index]);
	s2tt = granule_map(g_tbl, SLOT_DELEGATED);
	assert(s2tt != NULL);


	if (s2tte_is_unassigned_empty(parent_s2tte)) {
		s2tt_init_unassigned_empty(s2tt);

		/*
		 * Increase the refcount of the parent, the granule was
		 * locked while table walking and hand-over-hand locking.
		 * Atomicity and acquire/release semantics not required because
		 * the table is accessed always locked.
		 */
		__granule_get(wi.g_llt);

	} else if (s2tte_is_unassigned_ram(parent_s2tte)) {
		s2tt_init_unassigned_ram(s2tt);
		__granule_get(wi.g_llt);

	} else if (s2tte_is_unassigned_ns(parent_s2tte)) {
		s2tt_init_unassigned_ns(s2tt);
		__granule_get(wi.g_llt);

	} else if (s2tte_is_unassigned_destroyed(parent_s2tte)) {
		s2tt_init_unassigned_destroyed(s2tt);
		__granule_get(wi.g_llt);

	} else if (s2tte_is_assigned_destroyed(parent_s2tte, level - 1L)) {
		unsigned long block_pa;

		/*
		 * We should observe parent assigned s2tte only when
		 * we create tables above this level.
		 */
		assert(level > RTT_MIN_BLOCK_LEVEL);

		block_pa = s2tte_pa(parent_s2tte, level - 1L);

		s2tt_init_assigned_destroyed(s2tt, block_pa, level);

		/*
		 * Increase the refcount to mark the granule as in-use. refcount
		 * is incremented by S2TTES_PER_S2TT (ref RTT unfolding).
		 */
		__granule_refcount_inc(g_tbl, S2TTES_PER_S2TT);

	} else if (s2tte_is_assigned_empty(parent_s2tte, level - 1L)) {
		unsigned long block_pa;

		/*
		 * We should observe parent assigned s2tte only when
		 * we create tables above this level.
		 */
		assert(level > RTT_MIN_BLOCK_LEVEL);

		block_pa = s2tte_pa(parent_s2tte, level - 1L);

		s2tt_init_assigned_empty(s2tt, block_pa, level);

		/*
		 * Increase the refcount to mark the granule as in-use. refcount
		 * is incremented by S2TTES_PER_S2TT (ref RTT unfolding).
		 */
		__granule_refcount_inc(g_tbl, S2TTES_PER_S2TT);

	} else if (s2tte_is_assigned_ram(parent_s2tte, level - 1L)) {
		unsigned long block_pa;

		/*
		 * We should observe parent valid s2tte only when
		 * we create tables above this level.
		 */
		assert(level > RTT_MIN_BLOCK_LEVEL);

		/*
		 * Break before make. This may cause spurious S2 aborts.
		 */
		s2tte_write(&parent_s2tt[wi.index], 0UL);
		invalidate_block(&s2_ctx, map_addr);

		block_pa = s2tte_pa(parent_s2tte, level - 1L);

		s2tt_init_assigned_ram(s2tt, block_pa, level);

		/*
		 * Increase the refcount to mark the granule as in-use. refcount
		 * is incremented by S2TTES_PER_S2TT (ref RTT unfolding).
		 */
		__granule_refcount_inc(g_tbl, S2TTES_PER_S2TT);

	} else if (s2tte_is_assigned_ns(parent_s2tte, level - 1L)) {
		unsigned long block_pa;

		/*
		 * We should observe parent assigned_ns s2tte only when
		 * we create tables above this level.
		 */
		assert(level > RTT_MIN_BLOCK_LEVEL);

		/*
		 * Break before make. This may cause spurious S2 aborts.
		 */
		s2tte_write(&parent_s2tt[wi.index], 0UL);
		invalidate_block(&s2_ctx, map_addr);

		block_pa = s2tte_pa(parent_s2tte, level - 1L);

		s2tt_init_assigned_ns(s2tt, block_pa, level);

		/*
		 * Increase the refcount to mark the granule as in-use. refcount
		 * is incremented by S2TTES_PER_S2TT (ref RTT unfolding).
		 */
		__granule_refcount_inc(g_tbl, S2TTES_PER_S2TT);

	} else if (s2tte_is_table(parent_s2tte, level - 1L)) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned int)(level - 1L));
		goto out_unmap_table;

	} else {
		assert(false);
	}

	ret = RMI_SUCCESS;

	granule_set_state(g_tbl, GRANULE_STATE_RTT);

	parent_s2tte = s2tte_create_table(rtt_addr, level - 1L);
	s2tte_write(&parent_s2tt[wi.index], parent_s2tte);

out_unmap_table:
	buffer_unmap(s2tt);
	buffer_unmap(parent_s2tt);
out_unlock_llt:
	granule_unlock(wi.g_llt);
	granule_unlock(g_tbl);
	return ret;
}

void smc_rtt_fold(unsigned long rd_addr,
		  unsigned long map_addr,
		  unsigned long ulevel,
		  struct smc_result *res)
{
	struct granule *g_rd;
	struct granule *g_tbl;
	struct rd *rd;
	struct granule *g_table_root;
	struct rtt_walk wi;
	unsigned long *table, *parent_s2tt, parent_s2tte;
	long level = (long)ulevel;
	unsigned long ipa_bits, rtt_addr;
	unsigned long ret;
	struct realm_s2_context s2_ctx;
	int sl;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	rd = granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_rtt_structure_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	g_table_root = rd->s2_ctx.g_rtt;
	sl = realm_rtt_starting_level(rd);
	ipa_bits = realm_ipa_bits(rd);
	s2_ctx = rd->s2_ctx;
	buffer_unmap(rd);
	granule_lock(g_table_root, GRANULE_STATE_RTT);
	granule_unlock(g_rd);

	rtt_walk_lock_unlock(g_table_root, sl, ipa_bits,
				map_addr, level - 1L, &wi);
	if (wi.last_level != level - 1L) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned int)wi.last_level);
		goto out_unlock_parent_table;
	}

	parent_s2tt = granule_map(wi.g_llt, SLOT_RTT);
	assert(parent_s2tt != NULL);

	parent_s2tte = s2tte_read(&parent_s2tt[wi.index]);
	if (!s2tte_is_table(parent_s2tte, level - 1L)) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned int)(level - 1L));
		goto out_unmap_parent_table;
	}

	rtt_addr = s2tte_pa_table(parent_s2tte, level - 1L);
	g_tbl = find_lock_granule(rtt_addr, GRANULE_STATE_RTT);

	/*
	 * A table descriptor S2TTE always points to a TABLE granule.
	 */
	assert(g_tbl != NULL);

	table = granule_map(g_tbl, SLOT_RTT2);
	assert(table != NULL);

	/*
	 * The command can succeed only if all 512 S2TTEs are of the same type.
	 * We first check the table's ref. counter to speed up the case when
	 * the host makes a guess whether a memory region can be folded.
	 */
	if (g_tbl->refcount == 0UL) {
		if (table_is_unassigned_destroyed_block(table)) {
			parent_s2tte = s2tte_create_unassigned_destroyed();
		} else if (table_is_unassigned_empty_block(table)) {
			parent_s2tte = s2tte_create_unassigned_empty();
		} else if (table_is_unassigned_ram_block(table)) {
			parent_s2tte = s2tte_create_unassigned_ram();
		} else if (table_is_unassigned_ns_block(table)) {
			parent_s2tte = s2tte_create_unassigned_ns();
		} else if (table_maps_assigned_ns_block(table, level)) {
			unsigned long s2tte = s2tte_read(&table[0]);
			unsigned long block_pa = s2tte_pa(s2tte, level);

			parent_s2tte = s2tte_create_assigned_ns(block_pa,
								level - 1L);
		} else {
			/*
			 * The table holds a mixture of destroyed and
			 * unassigned entries.
			 */
			ret = pack_return_code(RMI_ERROR_RTT,
						(unsigned int)level);
			goto out_unmap_table;
		}
		__granule_put(wi.g_llt);
	} else if (g_tbl->refcount == S2TTES_PER_S2TT) {

		unsigned long s2tte, block_pa;

		/* The RMM specification does not allow creating block
		 * entries less than RTT_MIN_BLOCK_LEVEL even though
		 * permitted by the Arm Architecture.
		 * Hence ensure that the table being folded is at a level
		 * higher than the RTT_MIN_BLOCK_LEVEL.
		 *
		 * A fully populated table cannot be destroyed if that
		 * would create a block mapping below RTT_MIN_BLOCK_LEVEL.
		 */
		if (level <= RTT_MIN_BLOCK_LEVEL) {
			ret = pack_return_code(RMI_ERROR_RTT,
						(unsigned int)wi.last_level);
			goto out_unmap_table;
		}

		s2tte = s2tte_read(&table[0]);
		block_pa = s2tte_pa(s2tte, level);

		/*
		 * The table must also refer to a contiguous block through the
		 * same type of s2tte, either Assigned or Valid.
		 */
		if (table_maps_assigned_empty_block(table, level)) {
			parent_s2tte = s2tte_create_assigned_empty(block_pa,
								   level - 1L);
		} else if (table_maps_assigned_ram_block(table, level)) {
			parent_s2tte = s2tte_create_assigned_ram(block_pa,
								 level - 1L);
		} else if (table_maps_assigned_destroyed_block(table, level)) {
			parent_s2tte = s2tte_create_assigned_destroyed(block_pa,
								 level - 1L);
		/* The table contains mixed entries that cannot be folded */
		} else {
			ret = pack_return_code(RMI_ERROR_RTT,
						(unsigned int)level);
			goto out_unmap_table;
		}

		__granule_refcount_dec(g_tbl, S2TTES_PER_S2TT);
	} else {
		/*
		 * The table holds a mixture of different types of s2ttes.
		 */
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned int)level);
		goto out_unmap_table;
	}

	ret = RMI_SUCCESS;
	res->x[1] = rtt_addr;

	/*
	 * Break before make.
	 */
	s2tte_write(&parent_s2tt[wi.index], 0UL);

	if (s2tte_is_assigned_ram(parent_s2tte, level - 1L) ||
	    s2tte_is_assigned_ns(parent_s2tte, level - 1L)) {
		invalidate_pages_in_block(&s2_ctx, map_addr);
	} else {
		invalidate_block(&s2_ctx, map_addr);
	}

	s2tte_write(&parent_s2tt[wi.index], parent_s2tte);

	granule_memzero_mapped(table);
	granule_set_state(g_tbl, GRANULE_STATE_DELEGATED);

out_unmap_table:
	buffer_unmap(table);
	granule_unlock(g_tbl);
out_unmap_parent_table:
	buffer_unmap(parent_s2tt);
out_unlock_parent_table:
	granule_unlock(wi.g_llt);
	res->x[0] = ret;
}

void smc_rtt_destroy(unsigned long rd_addr,
		     unsigned long map_addr,
		     unsigned long ulevel,
		     struct smc_result *res)
{
	struct granule *g_rd;
	struct granule *g_tbl;
	struct rd *rd;
	struct granule *g_table_root;
	struct rtt_walk wi;
	unsigned long *table, *parent_s2tt, parent_s2tte;
	long level = (long)ulevel;
	unsigned long ipa_bits, rtt_addr;
	unsigned long ret;
	struct realm_s2_context s2_ctx;
	int sl;
	bool in_par, skip_non_live = false;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		res->x[2] = 0UL;
		return;
	}

	rd = granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_rtt_structure_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		res->x[2] = 0UL;
		return;
	}

	g_table_root = rd->s2_ctx.g_rtt;
	sl = realm_rtt_starting_level(rd);
	ipa_bits = realm_ipa_bits(rd);
	s2_ctx = rd->s2_ctx;
	in_par = addr_in_par(rd, map_addr);
	buffer_unmap(rd);
	granule_lock(g_table_root, GRANULE_STATE_RTT);
	granule_unlock(g_rd);

	rtt_walk_lock_unlock(g_table_root, sl, ipa_bits,
				map_addr, level - 1L, &wi);

	parent_s2tt = granule_map(wi.g_llt, SLOT_RTT);
	assert(parent_s2tt != NULL);

	parent_s2tte = s2tte_read(&parent_s2tt[wi.index]);

	if ((wi.last_level != level - 1L) ||
	    !s2tte_is_table(parent_s2tte, level - 1L)) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned int)wi.last_level);
		skip_non_live = true;
		goto out_unmap_parent_table;
	}

	rtt_addr = s2tte_pa_table(parent_s2tte, level - 1L);

	/*
	 * Lock the RTT granule. The 'rtt_addr' is verified, thus can be treated
	 * as an internal granule.
	 */
	g_tbl = find_lock_granule(rtt_addr, GRANULE_STATE_RTT);

	/*
	 * A table descriptor S2TTE always points to a TABLE granule.
	 */
	assert(g_tbl != NULL);

	/*
	 * Read the refcount value. RTT granule is always accessed locked, thus
	 * the refcount can be accessed without atomic operations.
	 */
	if (g_tbl->refcount != 0UL) {
		ret = pack_return_code(RMI_ERROR_RTT, (unsigned int)level);
		goto out_unlock_table;
	}

	ret = RMI_SUCCESS;
	res->x[1] = rtt_addr;
	skip_non_live = true;

	table = granule_map(g_tbl, SLOT_RTT2);
	assert(table != NULL);

	if (in_par) {
		parent_s2tte = s2tte_create_unassigned_destroyed();
	} else {
		parent_s2tte = s2tte_create_unassigned_ns();
	}

	__granule_put(wi.g_llt);

	/*
	 * Break before make. Note that this may cause spurious S2 aborts.
	 */
	s2tte_write(&parent_s2tt[wi.index], 0UL);
	invalidate_block(&s2_ctx, map_addr);
	s2tte_write(&parent_s2tt[wi.index], parent_s2tte);

	granule_memzero_mapped(table);
	granule_set_state(g_tbl, GRANULE_STATE_DELEGATED);

	buffer_unmap(table);
out_unlock_table:
	granule_unlock(g_tbl);
out_unmap_parent_table:
	if (skip_non_live) {
		res->x[2] = skip_non_live_entries(map_addr, parent_s2tt, &wi);
	} else {
		res->x[2] = map_addr;
	}
	buffer_unmap(parent_s2tt);
	granule_unlock(wi.g_llt);
	res->x[0] = ret;
}

enum map_unmap_ns_op {
	MAP_NS,
	UNMAP_NS
};

/*
 * We don't hold a reference on the NS granule when it is
 * mapped into a realm. Instead we rely on the guarantees
 * provided by the architecture to ensure that a NS access
 * to a protected granule is prohibited even within the realm.
 */
static void map_unmap_ns(unsigned long rd_addr,
			 unsigned long map_addr,
			 long level,
			 unsigned long host_s2tte,
			 enum map_unmap_ns_op op,
			 struct smc_result *res)
{
	struct granule *g_rd;
	struct rd *rd;
	struct granule *g_table_root;
	unsigned long *s2tt, s2tte;
	struct rtt_walk wi;
	unsigned long ipa_bits;
	struct realm_s2_context s2_ctx;
	int sl;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	rd = granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_rtt_map_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	g_table_root = rd->s2_ctx.g_rtt;
	sl = realm_rtt_starting_level(rd);
	ipa_bits = realm_ipa_bits(rd);

	/* Check if map_addr is outside PAR */
	if (addr_in_par(rd, map_addr)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	s2_ctx = rd->s2_ctx;
	buffer_unmap(rd);

	granule_lock(g_table_root, GRANULE_STATE_RTT);
	granule_unlock(g_rd);

	rtt_walk_lock_unlock(g_table_root, sl, ipa_bits,
				map_addr, level, &wi);

	/*
	 * For UNMAP_NS, we need to map the table and look
	 * for the end of the non-live region.
	 */
	if ((op == MAP_NS) && (wi.last_level != level)) {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned int)wi.last_level);
		goto out_unlock_llt;
	}

	s2tt = granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	s2tte = s2tte_read(&s2tt[wi.index]);

	if (op == MAP_NS) {
		if (!s2tte_is_unassigned_ns(s2tte)) {
			res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned int)level);
			goto out_unmap_table;
		}

		s2tte = s2tte_create_assigned_ns(host_s2tte, level);
		s2tte_write(&s2tt[wi.index], s2tte);

	} else if (op == UNMAP_NS) {
		/*
		 * The following check also verifies that map_addr is outside
		 * PAR, as valid_NS s2tte may only cover outside PAR IPA range.
		 */
		bool assigned_ns = s2tte_is_assigned_ns(s2tte, wi.last_level);

		if ((wi.last_level != level) || !assigned_ns) {
			res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned int)wi.last_level);
			goto out_unmap_table;
		}

		s2tte = s2tte_create_unassigned_ns();
		s2tte_write(&s2tt[wi.index], s2tte);
		if (level == RTT_PAGE_LEVEL) {
			invalidate_page(&s2_ctx, map_addr);
		} else {
			invalidate_block(&s2_ctx, map_addr);
		}
	}

	res->x[0] = RMI_SUCCESS;

out_unmap_table:
	if (op == UNMAP_NS) {
		res->x[1] = skip_non_live_entries(map_addr, s2tt, &wi);
	}
	buffer_unmap(s2tt);
out_unlock_llt:
	granule_unlock(wi.g_llt);
}

unsigned long smc_rtt_map_unprotected(unsigned long rd_addr,
				      unsigned long map_addr,
				      unsigned long ulevel,
				      unsigned long s2tte)
{
	long level = (long)ulevel;
	struct smc_result res;

	if (!host_ns_s2tte_is_valid(s2tte, level)) {
		return RMI_ERROR_INPUT;
	}

	map_unmap_ns(rd_addr, map_addr, level, s2tte, MAP_NS, &res);
	return res.x[0];
}

void smc_rtt_unmap_unprotected(unsigned long rd_addr,
				unsigned long map_addr,
				unsigned long ulevel,
				struct smc_result *res)
{
	return map_unmap_ns(rd_addr, map_addr, (long)ulevel, 0UL, UNMAP_NS, res);
}

void smc_rtt_read_entry(unsigned long rd_addr,
			unsigned long map_addr,
			unsigned long ulevel,
			struct smc_result *res)
{
	struct granule *g_rd, *g_rtt_root;
	struct rd *rd;
	struct rtt_walk wi;
	unsigned long *s2tt, s2tte;
	unsigned long ipa_bits;
	long level = (long)ulevel;
	int sl;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	rd = granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_rtt_entry_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	g_rtt_root = rd->s2_ctx.g_rtt;
	sl = realm_rtt_starting_level(rd);
	ipa_bits = realm_ipa_bits(rd);
	buffer_unmap(rd);

	granule_lock(g_rtt_root, GRANULE_STATE_RTT);
	granule_unlock(g_rd);

	rtt_walk_lock_unlock(g_rtt_root, sl, ipa_bits,
				map_addr, level, &wi);
	s2tt = granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	s2tte = s2tte_read(&s2tt[wi.index]);
	res->x[1] =  wi.last_level;

	if (s2tte_is_unassigned_empty(s2tte)) {
		res->x[2] = RMI_UNASSIGNED;
		res->x[3] = 0UL;
		res->x[4] = RIPAS_EMPTY;
	} else if (s2tte_is_unassigned_ram(s2tte)) {
		res->x[2] = RMI_UNASSIGNED;
		res->x[3] = 0UL;
		res->x[4] = RIPAS_RAM;
	} else if (s2tte_is_unassigned_destroyed(s2tte)) {
		res->x[2] = RMI_UNASSIGNED;
		res->x[3] = 0UL;
		res->x[4] = RIPAS_DESTROYED;
	} else if (s2tte_is_assigned_empty(s2tte, wi.last_level)) {
		res->x[2] = RMI_ASSIGNED;
		res->x[3] = s2tte_pa(s2tte, wi.last_level);
		res->x[4] = RIPAS_EMPTY;
	} else if (s2tte_is_assigned_ram(s2tte, wi.last_level)) {
		res->x[2] = RMI_ASSIGNED;
		res->x[3] = s2tte_pa(s2tte, wi.last_level);
		res->x[4] = RIPAS_RAM;
	} else if (s2tte_is_assigned_destroyed(s2tte, wi.last_level)) {
		res->x[2] = RMI_ASSIGNED;
		res->x[3] = 0UL;
		res->x[4] = RIPAS_DESTROYED;
	} else if (s2tte_is_unassigned_ns(s2tte)) {
		res->x[2] = RMI_UNASSIGNED;
		res->x[3] = 0UL;
		res->x[4] = RIPAS_EMPTY;
	} else if (s2tte_is_assigned_ns(s2tte, wi.last_level)) {
		res->x[2] = RMI_ASSIGNED;
		res->x[3] = host_ns_s2tte(s2tte, wi.last_level);
		res->x[4] = RIPAS_EMPTY;
	} else if (s2tte_is_table(s2tte, wi.last_level)) {
		res->x[2] = RMI_TABLE;
		res->x[3] = s2tte_pa_table(s2tte, wi.last_level);
		res->x[4] = RIPAS_EMPTY;
	} else {
		assert(false);
	}

	buffer_unmap(s2tt);
	granule_unlock(wi.g_llt);

	res->x[0] = RMI_SUCCESS;
}

static void data_granule_measure(struct rd *rd, void *data,
				 unsigned long ipa,
				 unsigned long flags)
{
	struct measurement_desc_data measure_desc = {0};

	/* Initialize the measurement descriptior structure */
	measure_desc.desc_type = MEASURE_DESC_TYPE_DATA;
	measure_desc.len = sizeof(struct measurement_desc_data);
	measure_desc.ipa = ipa;
	measure_desc.flags = flags;
	memcpy(measure_desc.rim,
	       &rd->measurement[RIM_MEASUREMENT_SLOT],
	       measurement_get_size(rd->algorithm));

	if (flags == RMI_MEASURE_CONTENT) {
		/*
		 * Hashing the data granules and store the result in the
		 * measurement descriptor structure.
		 */
		measurement_hash_compute(rd->algorithm,
					data,
					GRANULE_SIZE,
					measure_desc.content);
	}

	/*
	 * Hashing the measurement descriptor structure; the result is the
	 * updated RIM.
	 */
	measurement_hash_compute(rd->algorithm,
			       &measure_desc,
			       sizeof(measure_desc),
			       rd->measurement[RIM_MEASUREMENT_SLOT]);
}

static unsigned long validate_data_create_unknown(unsigned long map_addr,
						  struct rd *rd)
{
	if (!addr_in_par(rd, map_addr)) {
		return RMI_ERROR_INPUT;
	}

	if (!validate_map_addr(map_addr, RTT_PAGE_LEVEL, rd)) {
		return RMI_ERROR_INPUT;
	}

	return RMI_SUCCESS;
}

static unsigned long validate_data_create(unsigned long map_addr,
					  struct rd *rd)
{
	if (get_rd_state_locked(rd) != REALM_STATE_NEW) {
		return RMI_ERROR_REALM;
	}

	return validate_data_create_unknown(map_addr, rd);
}

/*
 * Implements both RMI_DATA_CREATE and RMI_DATA_CREATE_UNKNOWN
 *
 * if @g_src == NULL, implements RMI_DATA_CREATE_UNKNOWN
 * and RMI_DATA_CREATE otherwise.
 */
static unsigned long data_create(unsigned long rd_addr,
				 unsigned long data_addr,
				 unsigned long map_addr,
				 struct granule *g_src,
				 unsigned long flags)
{
	struct granule *g_data;
	struct granule *g_rd;
	struct granule *g_table_root;
	struct rd *rd;
	struct rtt_walk wi;
	unsigned long s2tte, *s2tt;
	enum granule_state new_data_state = GRANULE_STATE_DELEGATED;
	unsigned long ipa_bits;
	unsigned long ret;
	int __unused meas_ret;
	int sl;

	if (!find_lock_two_granules(data_addr,
				    GRANULE_STATE_DELEGATED,
				    &g_data,
				    rd_addr,
				    GRANULE_STATE_RD,
				    &g_rd)) {
		return RMI_ERROR_INPUT;
	}

	rd = granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	ret = (g_src != NULL) ?
		validate_data_create(map_addr, rd) :
		validate_data_create_unknown(map_addr, rd);

	if (ret != RMI_SUCCESS) {
		goto out_unmap_rd;
	}

	g_table_root = rd->s2_ctx.g_rtt;
	sl = realm_rtt_starting_level(rd);
	ipa_bits = realm_ipa_bits(rd);
	granule_lock(g_table_root, GRANULE_STATE_RTT);
	rtt_walk_lock_unlock(g_table_root, sl, ipa_bits,
			     map_addr, RTT_PAGE_LEVEL, &wi);
	if (wi.last_level != RTT_PAGE_LEVEL) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned int)wi.last_level);
		goto out_unlock_ll_table;
	}

	s2tt = granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	s2tte = s2tte_read(&s2tt[wi.index]);

	if (g_src != NULL) {
		bool ns_access_ok;
		void *data;

		if (!s2tte_is_unassigned_ram(s2tte)) {
			ret = pack_return_code(RMI_ERROR_RTT, RTT_PAGE_LEVEL);
			goto out_unmap_ll_table;
		}

		data = granule_map(g_data, SLOT_DELEGATED);
		assert(data != NULL);

		ns_access_ok = ns_buffer_read(SLOT_NS, g_src, 0U,
					      GRANULE_SIZE, data);
		if (!ns_access_ok) {
			/*
			 * Some data may be copied before the failure. Zero
			 * g_data granule as it will remain in delegated state.
			 */
			(void)memset(data, 0, GRANULE_SIZE);
			buffer_unmap(data);
			ret = RMI_ERROR_INPUT;
			goto out_unmap_ll_table;
		}

		data_granule_measure(rd, data, map_addr, flags);
		buffer_unmap(data);

	} else if (!s2tte_is_unassigned(s2tte)) {
		ret = pack_return_code(RMI_ERROR_RTT, RTT_PAGE_LEVEL);
		goto out_unmap_ll_table;
	}

	new_data_state = GRANULE_STATE_DATA;

	s2tte = s2tte_create_assigned_ram(data_addr, RTT_PAGE_LEVEL);

	s2tte_write(&s2tt[wi.index], s2tte);
	__granule_get(wi.g_llt);

	ret = RMI_SUCCESS;

out_unmap_ll_table:
	buffer_unmap(s2tt);
out_unlock_ll_table:
	granule_unlock(wi.g_llt);
out_unmap_rd:
	buffer_unmap(rd);
	granule_unlock(g_rd);
	granule_unlock_transition(g_data, new_data_state);
	return ret;
}

unsigned long smc_data_create(unsigned long rd_addr,
			      unsigned long data_addr,
			      unsigned long map_addr,
			      unsigned long src_addr,
			      unsigned long flags)
{
	struct granule *g_src;

	if (flags != RMI_NO_MEASURE_CONTENT && flags != RMI_MEASURE_CONTENT) {
		return RMI_ERROR_INPUT;
	}

	g_src = find_granule(src_addr);
	if ((g_src == NULL) || (g_src->state != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	return data_create(rd_addr, data_addr, map_addr, g_src, flags);
}

unsigned long smc_data_create_unknown(unsigned long rd_addr,
				      unsigned long data_addr,
				      unsigned long map_addr)
{
	return data_create(rd_addr, data_addr, map_addr, NULL, 0);
}

void smc_data_destroy(unsigned long rd_addr,
		      unsigned long map_addr,
		      struct smc_result *res)
{
	struct granule *g_data;
	struct granule *g_rd;
	struct granule *g_table_root;
	struct rtt_walk wi;
	unsigned long data_addr, s2tte, *s2tt;
	struct rd *rd;
	unsigned long ipa_bits;
	struct realm_s2_context s2_ctx;
	int sl;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		res->x[2] = 0UL;
		return;
	}

	rd = granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_map_addr(map_addr, RTT_PAGE_LEVEL, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		res->x[2] = 0UL;
		return;
	}

	g_table_root = rd->s2_ctx.g_rtt;
	sl = realm_rtt_starting_level(rd);
	ipa_bits = realm_ipa_bits(rd);
	s2_ctx = rd->s2_ctx;
	buffer_unmap(rd);

	granule_lock(g_table_root, GRANULE_STATE_RTT);
	granule_unlock(g_rd);

	rtt_walk_lock_unlock(g_table_root, sl, ipa_bits,
				map_addr, RTT_PAGE_LEVEL, &wi);

	s2tt = granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	if (wi.last_level != RTT_PAGE_LEVEL) {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned int)wi.last_level);
		goto out_unmap_ll_table;
	}

	s2tte = s2tte_read(&s2tt[wi.index]);

	if (s2tte_is_assigned_ram(s2tte, RTT_PAGE_LEVEL)) {
		data_addr = s2tte_pa(s2tte, RTT_PAGE_LEVEL);
		s2tte = s2tte_create_unassigned_destroyed();
		s2tte_write(&s2tt[wi.index], s2tte);
		invalidate_page(&s2_ctx, map_addr);
	} else if (s2tte_is_assigned_empty(s2tte, RTT_PAGE_LEVEL)) {
		data_addr = s2tte_pa(s2tte, RTT_PAGE_LEVEL);
		s2tte = s2tte_create_unassigned_empty();
		s2tte_write(&s2tt[wi.index], s2tte);
	} else {
		res->x[0] = pack_return_code(RMI_ERROR_RTT, RTT_PAGE_LEVEL);
		goto out_unmap_ll_table;
	}

	__granule_put(wi.g_llt);

	/*
	 * Lock the data granule and check expected state. Correct locking order
	 * is guaranteed because granule address is obtained from a locked
	 * granule by table walk. This lock needs to be acquired before a state
	 * transition to or from GRANULE_STATE_DATA for granule address can happen.
	 */
	g_data = find_lock_granule(data_addr, GRANULE_STATE_DATA);
	assert(g_data != NULL);
	granule_memzero(g_data, SLOT_DELEGATED);
	granule_unlock_transition(g_data, GRANULE_STATE_DELEGATED);

	res->x[0] = RMI_SUCCESS;
	res->x[1] = data_addr;
out_unmap_ll_table:
	res->x[2] = skip_non_live_entries(map_addr, s2tt, &wi);
	buffer_unmap(s2tt);
	granule_unlock(wi.g_llt);
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
static int update_ripas(unsigned long *s2ttep, unsigned long level,
			enum ripas ripas_val,
			enum ripas_change_destroyed change_destroyed)
{
	unsigned long pa, s2tte = s2tte_read(s2ttep);
	int ret = 0;

	if (!s2tte_has_ripas(s2tte, level)) {
		return -1;
	}

	if (ripas_val == RIPAS_RAM) {
		if (s2tte_is_unassigned_empty(s2tte)) {
			s2tte = s2tte_create_unassigned_ram();
		} else if (s2tte_is_unassigned_destroyed(s2tte)) {
			if (change_destroyed == CHANGE_DESTROYED) {
				s2tte = s2tte_create_unassigned_ram();
			} else {
				return -1;
			}
		} else if (s2tte_is_assigned_empty(s2tte, level)) {
			pa = s2tte_pa(s2tte, level);
			s2tte = s2tte_create_assigned_ram(pa, level);
		} else if (s2tte_is_assigned_destroyed(s2tte, level)) {
			if (change_destroyed == CHANGE_DESTROYED) {
				pa = s2tte_pa(s2tte, level);
				s2tte = s2tte_create_assigned_ram(pa, level);
			} else {
				return -1;
			}
		} else {
			/* No action is required */
			return 0;
		}
	} else if (ripas_val == RIPAS_EMPTY) {
		if (s2tte_is_unassigned_ram(s2tte)) {
			s2tte = s2tte_create_unassigned_empty();
		} else if (s2tte_is_unassigned_destroyed(s2tte)) {
			if (change_destroyed == CHANGE_DESTROYED) {
				s2tte = s2tte_create_unassigned_empty();
			} else {
				return -1;
			}
		} else if (s2tte_is_assigned_ram(s2tte, level)) {
			pa = s2tte_pa(s2tte, level);
			s2tte = s2tte_create_assigned_empty(pa, level);
			/* TLBI is required */
			ret = 1;
		} else if (s2tte_is_assigned_destroyed(s2tte, level)) {
			if (change_destroyed == CHANGE_DESTROYED) {
				pa = s2tte_pa(s2tte, level);
				s2tte = s2tte_create_assigned_empty(pa, level);
				/* TLBI is required */
				ret = 1;
			} else {
				return -1;
			}
		} else {
			/* No action is required */
			return 0;
		}
	}
	s2tte_write(s2ttep, s2tte);
	return ret;
}

static void ripas_granule_measure(struct rd *rd,
				  unsigned long base,
				  unsigned long top)
{
	struct measurement_desc_ripas measure_desc = {0};

	/* Initialize the measurement descriptior structure */
	measure_desc.desc_type = MEASURE_DESC_TYPE_RIPAS;
	measure_desc.len = sizeof(struct measurement_desc_ripas);
	measure_desc.base = base;
	measure_desc.top = top;
	(void)memcpy(measure_desc.rim,
		     &rd->measurement[RIM_MEASUREMENT_SLOT],
		     measurement_get_size(rd->algorithm));

	/*
	 * Hashing the measurement descriptor structure; the result is the
	 * updated RIM.
	 */
	measurement_hash_compute(rd->algorithm,
				 &measure_desc,
				 sizeof(measure_desc),
				 rd->measurement[RIM_MEASUREMENT_SLOT]);
}

void smc_rtt_init_ripas(unsigned long rd_addr,
			unsigned long base,
			unsigned long top,
			struct smc_result *res)
{
	struct granule *g_rd, *g_rtt_root;
	struct rd *rd;
	unsigned long ipa_bits, addr, map_size;
	struct rtt_walk wi;
	unsigned long s2tte, *s2tt;
	long level;
	unsigned long index;
	int sl;

	if (top <= base) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	rd = granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!validate_map_addr(base, RTT_PAGE_LEVEL, rd) ||
	    !validate_map_addr(top, RTT_PAGE_LEVEL, rd) ||
	    !addr_in_par(rd, base) || !addr_in_par(rd, top - GRANULE_SIZE)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (get_rd_state_locked(rd) != REALM_STATE_NEW) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = RMI_ERROR_REALM;
		return;
	}

	g_rtt_root = rd->s2_ctx.g_rtt;
	sl = realm_rtt_starting_level(rd);
	ipa_bits = realm_ipa_bits(rd);

	granule_lock(g_rtt_root, GRANULE_STATE_RTT);

	rtt_walk_lock_unlock(g_rtt_root, sl, ipa_bits,
				base, RTT_PAGE_LEVEL, &wi);
	level = wi.last_level;
	s2tt = granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	map_size = s2tte_map_size(level);
	addr = base & ~(map_size - 1UL);

	/*
	 * If the RTTE covers a range below "base", we need to go deeper.
	 */
	if (addr != base) {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned int)level);
		goto out_unmap_llt;
	}

	for (index = wi.index; index < S2TTES_PER_S2TT;
				index++, addr += map_size) {
		unsigned long next = addr + map_size;

		/*
		 * Break on "top_align" failure condition,
		 * or if this entry crosses the range.
		 */
		if (next > top) {
			break;
		}

		s2tte = s2tte_read(&s2tt[index]);
		if (s2tte_is_unassigned_empty(s2tte)) {
			s2tte = s2tte_create_unassigned_ram();
			s2tte_write(&s2tt[index], s2tte);
		} else if (!s2tte_is_unassigned_ram(s2tte)) {
			break;
		}
		ripas_granule_measure(rd, addr, next);
	}

	if (addr > base) {
		res->x[0] = RMI_SUCCESS;
		res->x[1] = addr;
	} else {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned int)level);
	}

out_unmap_llt:
	buffer_unmap(s2tt);
	buffer_unmap(rd);
	granule_unlock(wi.g_llt);
	granule_unlock(g_rd);
}

static void rtt_set_ripas_range(struct realm_s2_context *s2_ctx,
				unsigned long *s2tt,
				unsigned long base,
				unsigned long top,
				struct rtt_walk *wi,
				unsigned long ripas_val,
				enum ripas_change_destroyed change_destroyed,
				struct smc_result *res)
{
	unsigned long index;
	long level = wi->last_level;
	unsigned long map_size = s2tte_map_size(level);

	/* Align to the RTT level */
	unsigned long addr = base & ~(map_size - 1UL);

	/* Make sure we don't touch a range below the requested range */
	if (addr != base) {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned int)level);
		return;
	}

	for (index = wi->index; index < S2TTES_PER_S2TT; addr += map_size) {
		int ret;

		/*
		 * Break on "top_align" failure condition,
		 * or if this entry crosses the range.
		 */
		if ((addr + map_size) > top) {
			break;
		}

		ret = update_ripas(&s2tt[index++], level,
					ripas_val, change_destroyed);
		if (ret < 0) {
			break;
		}

		/* Handle TLBI */
		if (ret != 0) {
			if (level == RTT_PAGE_LEVEL) {
				invalidate_page(s2_ctx, addr);
			} else {
				invalidate_block(s2_ctx, addr);
			}
		}
	}

	if (addr > base) {
		res->x[0] = RMI_SUCCESS;
		res->x[1] = addr;
	} else {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned int)level);
	}
}

void smc_rtt_set_ripas(unsigned long rd_addr,
		       unsigned long rec_addr,
		       unsigned long base,
		       unsigned long top,
		       struct smc_result *res)
{
	struct granule *g_rd, *g_rec, *g_rtt_root;
	struct rec *rec;
	struct rd *rd;
	unsigned long ipa_bits;
	struct rtt_walk wi;
	unsigned long *s2tt;
	struct realm_s2_context s2_ctx;
	enum ripas ripas_val;
	enum ripas_change_destroyed change_destroyed;
	int sl;

	if (top <= base) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!find_lock_two_granules(rd_addr,
				   GRANULE_STATE_RD,
				   &g_rd,
				   rec_addr,
				   GRANULE_STATE_REC,
				   &g_rec)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (granule_refcount_read_acquire(g_rec) != 0UL) {
		res->x[0] = RMI_ERROR_REC;
		goto out_unlock_rec_rd;
	}

	rec = granule_map(g_rec, SLOT_REC);
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

	rd = granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	/*
	 * At this point, we know base == rec->set_ripas.addr
	 * and thus must be aligned to GRANULE size.
	 */
	assert(validate_map_addr(base, RTT_PAGE_LEVEL, rd));

	g_rtt_root = rd->s2_ctx.g_rtt;
	sl = realm_rtt_starting_level(rd);
	ipa_bits = realm_ipa_bits(rd);
	s2_ctx = rd->s2_ctx;

	granule_lock(g_rtt_root, GRANULE_STATE_RTT);

	/* Walk to the deepest level possible */
	rtt_walk_lock_unlock(g_rtt_root, sl, ipa_bits,
			     base, RTT_PAGE_LEVEL, &wi);

	/*
	 * Base has to be aligned to the level at which
	 * it is mapped in RTT.
	 */
	if (!validate_map_addr(base, wi.last_level, rd)) {
		res->x[0] = pack_return_code(RMI_ERROR_RTT,
						(unsigned int)wi.last_level);
		goto out_unlock_llt;
	}

	s2tt = granule_map(wi.g_llt, SLOT_RTT);
	assert(s2tt != NULL);

	rtt_set_ripas_range(&s2_ctx, s2tt, base, top, &wi,
				ripas_val, change_destroyed, res);

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

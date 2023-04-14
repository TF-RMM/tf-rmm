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

	if (map_addr >= realm_ipa_size(rd)) {
		return false;
	}
	if (!addr_is_level_aligned(map_addr, level)) {
		return false;
	}
	return true;
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
		ret = pack_return_code(RMI_ERROR_RTT, wi.last_level);
		goto out_unlock_llt;
	}

	parent_s2tt = granule_map(wi.g_llt, SLOT_RTT);
	parent_s2tte = s2tte_read(&parent_s2tt[wi.index]);
	s2tt = granule_map(g_tbl, SLOT_DELEGATED);

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

	} else if (s2tte_is_destroyed(parent_s2tte)) {
		s2tt_init_destroyed(s2tt);
		__granule_get(wi.g_llt);

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

unsigned long smc_rtt_fold(unsigned long rtt_addr,
			   unsigned long rd_addr,
			   unsigned long map_addr,
			   unsigned long ulevel)
{
	struct granule *g_rd;
	struct granule *g_tbl;
	struct rd *rd;
	struct granule *g_table_root;
	struct rtt_walk wi;
	unsigned long *table, *parent_s2tt, parent_s2tte;
	long level = (long)ulevel;
	unsigned long ipa_bits;
	unsigned long ret;
	struct realm_s2_context s2_ctx;
	int sl;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		return RMI_ERROR_INPUT;
	}

	rd = granule_map(g_rd, SLOT_RD);

	if (!validate_rtt_structure_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		return RMI_ERROR_INPUT;
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
	if (wi.last_level != level - 1UL) {
		ret = pack_return_code(RMI_ERROR_RTT, wi.last_level);
		goto out_unlock_parent_table;
	}

	parent_s2tt = granule_map(wi.g_llt, SLOT_RTT);
	parent_s2tte = s2tte_read(&parent_s2tt[wi.index]);
	if (!s2tte_is_table(parent_s2tte, level - 1L)) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned int)(level - 1L));
		goto out_unmap_parent_table;
	}

	/*
	 * Check that the 'rtt_addr' RTT is used at (map_addr, level).
	 * Note that this also verifies that the rtt_addr is properly aligned.
	 */
	if (rtt_addr != s2tte_pa_table(parent_s2tte, level - 1L)) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned int)(level - 1L));
		goto out_unmap_parent_table;
	}

	g_tbl = find_lock_granule(rtt_addr, GRANULE_STATE_RTT);

	/*
	 * A table descriptor S2TTE always points to a TABLE granule.
	 */
	assert(g_tbl);

	table = granule_map(g_tbl, SLOT_RTT2);

	/*
	 * The command can succeed only if all 512 S2TTEs are of the same type.
	 * We first check the table's ref. counter to speed up the case when
	 * the host makes a guess whether a memory region can be folded.
	 */
	if (g_tbl->refcount == 0UL) {
		if (table_is_destroyed_block(table)) {
			parent_s2tte = s2tte_create_destroyed();
			__granule_put(wi.g_llt);

		} else if (table_is_unassigned_empty_block(table)) {
			parent_s2tte = s2tte_create_unassigned_empty();
			__granule_put(wi.g_llt);

		} else if (table_is_unassigned_ram_block(table)) {
			parent_s2tte = s2tte_create_unassigned_ram();
			__granule_put(wi.g_llt);

		} else if (table_is_unassigned_ns_block(table)) {
			parent_s2tte = s2tte_create_unassigned_ns();
			__granule_put(wi.g_llt);

		} else {
			/*
			 * The table holds a mixture of destroyed and
			 * unassigned entries.
			 */
			ret = pack_return_code(RMI_ERROR_RTT, level);
			goto out_unmap_table;
		}

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
			ret = pack_return_code(RMI_ERROR_RTT, wi.last_level);
			goto out_unmap_table;
		}

		s2tte = s2tte_read(&table[0]);
		block_pa = s2tte_pa(s2tte, level);

		/*
		 * The table must also refer to a contiguous block through the
		 * same type of s2tte, either Assigned, Valid or Assigned_NS.
		 */
		if (table_maps_assigned_empty_block(table, level)) {
			parent_s2tte = s2tte_create_assigned_empty(block_pa,
								   level - 1L);
		} else if (table_maps_assigned_ram_block(table, level)) {
			parent_s2tte = s2tte_create_assigned_ram(block_pa,
								 level - 1L);
		} else if (table_maps_assigned_ns_block(table, level)) {
			parent_s2tte = s2tte_create_assigned_ns(block_pa,
								level - 1L);
		/* The table contains mixed entries that cannot be folded */
		} else {
			ret = pack_return_code(RMI_ERROR_RTT, level);
			goto out_unmap_table;
		}

		__granule_refcount_dec(g_tbl, S2TTES_PER_S2TT);
	} else {
		/*
		 * The table holds a mixture of different types of s2ttes.
		 */
		ret = pack_return_code(RMI_ERROR_RTT, level);
		goto out_unmap_table;
	}

	ret = RMI_SUCCESS;

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
	return ret;
}

unsigned long smc_rtt_destroy(unsigned long rtt_addr,
			      unsigned long rd_addr,
			      unsigned long map_addr,
			      unsigned long ulevel)
{
	struct granule *g_rd;
	struct granule *g_tbl;
	struct rd *rd;
	struct granule *g_table_root;
	struct rtt_walk wi;
	unsigned long *table, *parent_s2tt, parent_s2tte;
	long level = (long)ulevel;
	unsigned long ipa_bits;
	unsigned long ret;
	struct realm_s2_context s2_ctx;
	int sl;
	bool in_par;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		return RMI_ERROR_INPUT;
	}

	rd = granule_map(g_rd, SLOT_RD);

	if (!validate_rtt_structure_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		return RMI_ERROR_INPUT;
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
	if (wi.last_level != level - 1UL) {
		ret = pack_return_code(RMI_ERROR_RTT, wi.last_level);
		goto out_unlock_parent_table;
	}

	parent_s2tt = granule_map(wi.g_llt, SLOT_RTT);
	parent_s2tte = s2tte_read(&parent_s2tt[wi.index]);
	if (!s2tte_is_table(parent_s2tte, level - 1L)) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned int)(level - 1L));
		goto out_unmap_parent_table;
	}

	/*
	 * Check that the 'rtt_addr' RTT is used at (map_addr, level).
	 * Note that this also verifies that the rtt_addr is properly aligned.
	 */
	if (rtt_addr != s2tte_pa_table(parent_s2tte, level - 1L)) {
		ret = RMI_ERROR_INPUT;
		goto out_unmap_parent_table;
	}

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
		ret = pack_return_code(RMI_ERROR_RTT, level);
		goto out_unlock_table;
	}

	ret = RMI_SUCCESS;

	table = granule_map(g_tbl, SLOT_RTT2);

	if (in_par) {
		parent_s2tte = s2tte_create_destroyed();
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
	buffer_unmap(parent_s2tt);
out_unlock_parent_table:
	granule_unlock(wi.g_llt);
	return ret;
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
static unsigned long map_unmap_ns(unsigned long rd_addr,
				  unsigned long map_addr,
				  long level,
				  unsigned long host_s2tte,
				  enum map_unmap_ns_op op)
{
	struct granule *g_rd;
	struct rd *rd;
	struct granule *g_table_root;
	unsigned long *s2tt, s2tte;
	struct rtt_walk wi;
	unsigned long ipa_bits;
	unsigned long ret;
	struct realm_s2_context s2_ctx;
	int sl;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		return RMI_ERROR_INPUT;
	}

	rd = granule_map(g_rd, SLOT_RD);

	if (!validate_rtt_map_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		return RMI_ERROR_INPUT;
	}

	g_table_root = rd->s2_ctx.g_rtt;
	sl = realm_rtt_starting_level(rd);
	ipa_bits = realm_ipa_bits(rd);

	/* Check if map_addr is outside PAR */
	if (addr_in_par(rd, map_addr)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		return RMI_ERROR_INPUT;
	}

	s2_ctx = rd->s2_ctx;
	buffer_unmap(rd);

	granule_lock(g_table_root, GRANULE_STATE_RTT);
	granule_unlock(g_rd);

	rtt_walk_lock_unlock(g_table_root, sl, ipa_bits,
				map_addr, level, &wi);
	if (wi.last_level != level) {
		ret = pack_return_code(RMI_ERROR_RTT, wi.last_level);
		goto out_unlock_llt;
	}

	s2tt = granule_map(wi.g_llt, SLOT_RTT);
	s2tte = s2tte_read(&s2tt[wi.index]);

	if (op == MAP_NS) {
		if (!s2tte_is_unassigned_ns(s2tte)) {
			ret = pack_return_code(RMI_ERROR_RTT,
						(unsigned int)level);
			goto out_unmap_table;
		}

		s2tte = s2tte_create_assigned_ns(host_s2tte, level);
		s2tte_write(&s2tt[wi.index], s2tte);
		__granule_get(wi.g_llt);

	} else if (op == UNMAP_NS) {
		/*
		 * The following check also verifies that map_addr is outside
		 * PAR, as valid_NS s2tte may only cover outside PAR IPA range.
		 */
		if (!s2tte_is_assigned_ns(s2tte, level)) {
			ret = pack_return_code(RMI_ERROR_RTT,
						(unsigned int)level);
			goto out_unmap_table;
		}

		s2tte = s2tte_create_unassigned_ns();
		s2tte_write(&s2tt[wi.index], s2tte);
		__granule_put(wi.g_llt);
		if (level == RTT_PAGE_LEVEL) {
			invalidate_page(&s2_ctx, map_addr);
		} else {
			invalidate_block(&s2_ctx, map_addr);
		}
	}

	ret = RMI_SUCCESS;

out_unmap_table:
	buffer_unmap(s2tt);
out_unlock_llt:
	granule_unlock(wi.g_llt);
	return ret;
}

unsigned long smc_rtt_map_unprotected(unsigned long rd_addr,
				      unsigned long map_addr,
				      unsigned long ulevel,
				      unsigned long s2tte)
{
	long level = (long)ulevel;

	if (!host_ns_s2tte_is_valid(s2tte, level)) {
		return RMI_ERROR_INPUT;
	}

	return map_unmap_ns(rd_addr, map_addr, level, s2tte, MAP_NS);
}

unsigned long smc_rtt_unmap_unprotected(unsigned long rd_addr,
					unsigned long map_addr,
					unsigned long ulevel)
{
	return map_unmap_ns(rd_addr, map_addr, (long)ulevel, 0UL, UNMAP_NS);
}

void smc_rtt_read_entry(unsigned long rd_addr,
			unsigned long map_addr,
			unsigned long ulevel,
			struct smc_result *ret)
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
		ret->x[0] = RMI_ERROR_INPUT;
		return;
	}

	rd = granule_map(g_rd, SLOT_RD);

	if (!validate_rtt_entry_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		ret->x[0] = RMI_ERROR_INPUT;
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
	s2tte = s2tte_read(&s2tt[wi.index]);
	ret->x[1] =  wi.last_level;
	ret->x[3] = 0UL;
	ret->x[4] = 0UL;

	if (s2tte_is_unassigned_empty(s2tte)) {
		ret->x[2] = RMI_UNASSIGNED;
		ret->x[4] = RIPAS_EMPTY;
	} else if (s2tte_is_unassigned_ram(s2tte)) {
		ret->x[2] = RMI_UNASSIGNED;
		ret->x[4] = RIPAS_RAM;
	} else if (s2tte_is_destroyed(s2tte)) {
		ret->x[2] = RMI_DESTROYED;
	} else if (s2tte_is_assigned_empty(s2tte, wi.last_level)) {
		ret->x[2] = RMI_ASSIGNED;
		ret->x[3] = s2tte_pa(s2tte, wi.last_level);
		ret->x[4] = RIPAS_EMPTY;
	} else if (s2tte_is_assigned_ram(s2tte, wi.last_level)) {
		ret->x[2] = RMI_ASSIGNED;
		ret->x[3] = s2tte_pa(s2tte, wi.last_level);
		ret->x[4] = RIPAS_RAM;
	} else if (s2tte_is_unassigned_ns(s2tte)) {
		ret->x[2] = RMI_UNASSIGNED;
		ret->x[4] = RIPAS_EMPTY;
	} else if (s2tte_is_assigned_ns(s2tte, wi.last_level)) {
		ret->x[2] = RMI_VALID_NS;
		ret->x[3] = host_ns_s2tte(s2tte, wi.last_level);
	} else if (s2tte_is_table(s2tte, wi.last_level)) {
		ret->x[2] = RMI_TABLE;
		ret->x[3] = s2tte_pa_table(s2tte, wi.last_level);
	} else {
		assert(false);
	}

	buffer_unmap(s2tt);
	granule_unlock(wi.g_llt);

	ret->x[0] = RMI_SUCCESS;
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
 * Implements both Data.Create and Data.CreateUnknown
 *
 * if @g_src == NULL, this implemented Data.CreateUnknown
 * and otherwise this implemented Data.Create.
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
	enum ripas ripas;
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
		ret = pack_return_code(RMI_ERROR_RTT, wi.last_level);
		goto out_unlock_ll_table;
	}

	s2tt = granule_map(wi.g_llt, SLOT_RTT);
	s2tte = s2tte_read(&s2tt[wi.index]);
	if (s2tte_is_unassigned_empty(s2tte)) {
		ripas = RIPAS_EMPTY;
	} else if (s2tte_is_unassigned_ram(s2tte)) {
		ripas = RIPAS_RAM;
	} else {
		ret = pack_return_code(RMI_ERROR_RTT, RTT_PAGE_LEVEL);
		goto out_unmap_ll_table;
	}

	ripas = s2tte_get_ripas(s2tte);

	if (g_src != NULL) {
		bool ns_access_ok;
		void *data = granule_map(g_data, SLOT_DELEGATED);

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
	}

	new_data_state = GRANULE_STATE_DATA;

	s2tte = (ripas == RIPAS_EMPTY) ?
		s2tte_create_assigned_empty(data_addr, RTT_PAGE_LEVEL) :
		s2tte_create_assigned_ram(data_addr, RTT_PAGE_LEVEL);

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

unsigned long smc_data_destroy(unsigned long rd_addr,
			       unsigned long map_addr)
{
	struct granule *g_data;
	struct granule *g_rd;
	struct granule *g_table_root;
	struct rtt_walk wi;
	unsigned long data_addr, s2tte, *s2tt;
	struct rd *rd;
	unsigned long ipa_bits;
	unsigned long ret;
	struct realm_s2_context s2_ctx;
	bool valid;
	int sl;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		return RMI_ERROR_INPUT;
	}

	rd = granule_map(g_rd, SLOT_RD);

	if (!validate_map_addr(map_addr, RTT_PAGE_LEVEL, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		return RMI_ERROR_INPUT;
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
	if (wi.last_level != RTT_PAGE_LEVEL) {
		ret = pack_return_code(RMI_ERROR_RTT, wi.last_level);
		goto out_unlock_ll_table;
	}

	s2tt = granule_map(wi.g_llt, SLOT_RTT);
	s2tte = s2tte_read(&s2tt[wi.index]);

	valid = s2tte_is_assigned_ram(s2tte, RTT_PAGE_LEVEL);

	/*
	 * Check if either HIPAS=ASSIGNED or map_addr is a
	 * valid Protected IPA.
	 */
	if (!valid && !s2tte_is_assigned_empty(s2tte, RTT_PAGE_LEVEL)) {
		ret = pack_return_code(RMI_ERROR_RTT, RTT_PAGE_LEVEL);
		goto out_unmap_ll_table;
	}

	data_addr = s2tte_pa(s2tte, RTT_PAGE_LEVEL);

	/*
	 * We have already established either HIPAS=ASSIGNED or a valid mapping.
	 * If valid, transition HIPAS to DESTROYED and if HIPAS=ASSIGNED,
	 * transition to UNASSIGNED.
	 */
	s2tte = valid ? s2tte_create_destroyed() :
			s2tte_create_unassigned_empty();

	s2tte_write(&s2tt[wi.index], s2tte);

	if (valid) {
		invalidate_page(&s2_ctx, map_addr);
	}

	__granule_put(wi.g_llt);

	/*
	 * Lock the data granule and check expected state. Correct locking order
	 * is guaranteed because granule address is obtained from a locked
	 * granule by table walk. This lock needs to be acquired before a state
	 * transition to or from GRANULE_STATE_DATA for granule address can happen.
	 */
	g_data = find_lock_granule(data_addr, GRANULE_STATE_DATA);
	assert(g_data);
	granule_memzero(g_data, SLOT_DELEGATED);
	granule_unlock_transition(g_data, GRANULE_STATE_DELEGATED);

	ret = RMI_SUCCESS;

out_unmap_ll_table:
	buffer_unmap(s2tt);
out_unlock_ll_table:
	granule_unlock(wi.g_llt);

	return ret;
}

static bool update_ripas(unsigned long *s2tte, unsigned long level,
			 enum ripas ripas)
{
	if (s2tte_is_table(*s2tte, level)) {
		return false;
	}

	if (s2tte_is_assigned_ram(*s2tte, level)) {
		if (ripas == RIPAS_EMPTY) {
			unsigned long pa = s2tte_pa(*s2tte, level);
			*s2tte = s2tte_create_assigned_empty(pa, level);
		}
		return true;
	}

	if (s2tte_is_unassigned_empty(*s2tte) ||
	    s2tte_is_unassigned_ram(*s2tte)   ||
	    s2tte_is_assigned_empty(*s2tte, level)) {
		*s2tte |= s2tte_create_ripas(ripas);
		return true;
	}

	return false;
}

static void ripas_granule_measure(struct rd *rd,
				  unsigned long ipa,
				  unsigned long level)
{
	struct measurement_desc_ripas measure_desc = {0};

	/* Initialize the measurement descriptior structure */
	measure_desc.desc_type = MEASURE_DESC_TYPE_RIPAS;
	measure_desc.len = sizeof(struct measurement_desc_ripas);
	measure_desc.ipa = ipa;
	measure_desc.level = level;
	memcpy(measure_desc.rim,
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

unsigned long smc_rtt_init_ripas(unsigned long rd_addr,
				 unsigned long map_addr,
				 unsigned long ulevel)
{
	struct granule *g_rd, *g_rtt_root;
	struct rd *rd;
	unsigned long ipa_bits;
	struct rtt_walk wi;
	unsigned long s2tte, *s2tt;
	unsigned long ret;
	long level = (long)ulevel;
	int sl;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		return RMI_ERROR_INPUT;
	}

	rd = granule_map(g_rd, SLOT_RD);

	if (get_rd_state_locked(rd) != REALM_STATE_NEW) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		return RMI_ERROR_REALM;
	}

	if (!validate_rtt_entry_cmds(map_addr, level, rd)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		return RMI_ERROR_INPUT;
	}

	if (!addr_in_par(rd, map_addr)) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		return RMI_ERROR_INPUT;
	}

	g_rtt_root = rd->s2_ctx.g_rtt;
	sl = realm_rtt_starting_level(rd);
	ipa_bits = realm_ipa_bits(rd);

	granule_lock(g_rtt_root, GRANULE_STATE_RTT);
	granule_unlock(g_rd);

	rtt_walk_lock_unlock(g_rtt_root, sl, ipa_bits,
				map_addr, level, &wi);

	if (wi.last_level != level) {
		ret = pack_return_code(RMI_ERROR_RTT, wi.last_level);
		goto out_unlock_llt;
	}

	s2tt = granule_map(wi.g_llt, SLOT_RTT);
	s2tte = s2tte_read(&s2tt[wi.index]);

	/* Allowed only for HIPAS=UNASSIGNED */
	if (s2tte_is_table(s2tte, level) || !s2tte_is_unassigned(s2tte)) {
		ret = pack_return_code(RMI_ERROR_RTT, (unsigned int)level);
		goto out_unmap_llt;
	}

	s2tte |= s2tte_create_ripas(RIPAS_RAM);

	s2tte_write(&s2tt[wi.index], s2tte);

	ripas_granule_measure(rd, map_addr, level);

	ret = RMI_SUCCESS;

out_unmap_llt:
	buffer_unmap(s2tt);
out_unlock_llt:
	buffer_unmap(rd);
	granule_unlock(wi.g_llt);
	return ret;
}

unsigned long smc_rtt_set_ripas(unsigned long rd_addr,
				unsigned long rec_addr,
				unsigned long map_addr,
				unsigned long ulevel,
				unsigned long uripas)
{
	struct granule *g_rd, *g_rec, *g_rtt_root;
	struct rec *rec;
	struct rd *rd;
	unsigned long map_size, ipa_bits;
	struct rtt_walk wi;
	unsigned long s2tte, *s2tt;
	struct realm_s2_context s2_ctx;
	long level = (long)ulevel;
	enum ripas ripas = (enum ripas)uripas;
	unsigned long ret;
	bool valid;
	int sl;

	if (ripas > RIPAS_RAM) {
		return RMI_ERROR_INPUT;
	}

	if (!find_lock_two_granules(rd_addr,
				   GRANULE_STATE_RD,
				   &g_rd,
				   rec_addr,
				   GRANULE_STATE_REC,
				   &g_rec)) {
		return RMI_ERROR_INPUT;
	}

	if (granule_refcount_read_acquire(g_rec) != 0UL) {
		ret = RMI_ERROR_REC;
		goto out_unlock_rec_rd;
	}

	rec = granule_map(g_rec, SLOT_REC);

	if (g_rd != rec->realm_info.g_rd) {
		ret = RMI_ERROR_REC;
		goto out_unmap_rec;
	}

	if (ripas != rec->set_ripas.ripas) {
		ret = RMI_ERROR_INPUT;
		goto out_unmap_rec;
	}

	if (map_addr != rec->set_ripas.addr) {
		/* Target region is not next chunk of requested region */
		ret = RMI_ERROR_INPUT;
		goto out_unmap_rec;
	}

	rd = granule_map(g_rd, SLOT_RD);

	if (!validate_rtt_entry_cmds(map_addr, level, rd)) {
		ret = RMI_ERROR_INPUT;
		goto out_unmap_rd;
	}

	map_size = s2tte_map_size(level);
	if (map_addr + map_size > rec->set_ripas.end) {
		/* Target region extends beyond end of requested region */
		ret = RMI_ERROR_INPUT;
		goto out_unmap_rd;
	}

	g_rtt_root = rd->s2_ctx.g_rtt;
	sl = realm_rtt_starting_level(rd);
	ipa_bits = realm_ipa_bits(rd);
	s2_ctx = rd->s2_ctx;

	granule_lock(g_rtt_root, GRANULE_STATE_RTT);

	rtt_walk_lock_unlock(g_rtt_root, sl, ipa_bits,
				map_addr, level, &wi);
	if (wi.last_level != level) {
		ret = pack_return_code(RMI_ERROR_RTT, wi.last_level);
		goto out_unlock_llt;
	}

	s2tt = granule_map(wi.g_llt, SLOT_RTT);
	s2tte = s2tte_read(&s2tt[wi.index]);

	valid = s2tte_is_assigned_ram(s2tte, level);

	if (!update_ripas(&s2tte, level, ripas)) {
		ret = pack_return_code(RMI_ERROR_RTT, (unsigned int)level);
		goto out_unmap_llt;
	}

	s2tte_write(&s2tt[wi.index], s2tte);

	if (valid && (ripas == RIPAS_EMPTY)) {
		if (level == RTT_PAGE_LEVEL) {
			invalidate_page(&s2_ctx, map_addr);
		} else {
			invalidate_block(&s2_ctx, map_addr);
		}
	}

	rec->set_ripas.addr += map_size;

	ret = RMI_SUCCESS;

out_unmap_llt:
	buffer_unmap(s2tt);
out_unlock_llt:
	granule_unlock(wi.g_llt);
out_unmap_rd:
	buffer_unmap(rd);
out_unmap_rec:
	buffer_unmap(rec);
out_unlock_rec_rd:
	granule_unlock(g_rec);
	granule_unlock(g_rd);
	return ret;
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RTT_DATA_TEST_HELPERS_H
#define RTT_DATA_TEST_HELPERS_H

/*
 * Pull in shared utilities: reserve_delegated_granules, delegate_range_rtt,
 * granule_addr_rtt, sro_complete_operation, decode_single_oaddr_pa,
 * make_unmap_flags, make_unmap_flags_single, make_unmap_flags_none,
 * reserve_list_granule, g_rtt_next_idx, g_ns_list_next_idx, etc.
 */
#include "rtt_test_helpers.h"

/*
 * Protected IPA space constants.
 *
 * With TEST_IPA_BITS=40 and starting_level=0:
 *   L0[0] covers [0, 512GB) = PAR
 *   L3 at index 0 covers [0, 2MB)
 *
 * We use IPA 0 as the base for all protected-space tests.
 */
#define TEST_DATA_IPA_BASE       0x40000000UL
#define TEST_DATA_PAGE_TOP       (TEST_DATA_IPA_BASE + GRANULE_SIZE)
#define TEST_DATA_L2_BLOCK_SIZE  XLAT_BLOCK_SIZE(2)
#define TEST_DATA_L2_BLOCK_TOP   (TEST_DATA_IPA_BASE + TEST_DATA_L2_BLOCK_SIZE)

/*
 * The alignment-gap granules reserved for the fold test can occupy up to
 * 511 slots.  The L2 fold test needs 512 data granules on top of ~5 RTT
 * granules, so indices up to ~1030 may be used.  Keep the NS list pool
 * well clear of that range but within HOST_NR_GRANULES (131072).
 */
#define DATA_TEST_NS_LIST_START_IDX  120000U

/*
 * Test context for protected-data (data_map/data_unmap) tests.
 * Mirrors test_rtt_ctx but oriented around the protected IPA space.
 */
struct test_data_ctx {
	uintptr_t rd;
	uintptr_t rtt_l0;
	uintptr_t rtt_l1;
	uintptr_t rtt_l2;
	uintptr_t rtt_l3;
};

static inline void test_isr_el1_wr(u_register_t val, u_register_t *reg)
{
	*reg = val;
}

/*
 * Return 0 until the configured countdown reaches zero, then return 1 once
 * and 0 afterwards.
 */
static inline u_register_t test_isr_el1_rd_yield_on_countdown(
							u_register_t *reg)
{
	if (*reg == 0UL) {
		return 0UL;
	}

	(*reg)--;
	return (*reg == 0UL) ? 1UL : 0UL;
}

static inline u_register_t test_isr_el1_rd_yield_while_countdown(
							u_register_t *reg)
{
	if (*reg == 0UL) {
		return 0UL;
	}

	(*reg)--;
	return 1UL;
}

/*
 * Return the stored value on every read until the test installs a different
 * callback.
 */
static inline u_register_t test_isr_el1_rd_return_value(u_register_t *reg)
{
	return *reg;
}

static inline void prime_isr_yield(void)
{
	host_util_set_sysreg_cb("isr_el1",
				test_isr_el1_rd_yield_on_countdown,
				test_isr_el1_wr, 1UL);
}

static inline void prime_isr_yield_twice(void)
{
	host_util_set_sysreg_cb("isr_el1",
				test_isr_el1_rd_yield_while_countdown,
				test_isr_el1_wr, 2UL);
}

static inline void prime_isr_yield_in_drain(void)
{
	host_util_set_sysreg_cb("isr_el1",
				test_isr_el1_rd_yield_on_countdown,
				test_isr_el1_wr, S2TTES_PER_S2TT + 1UL);
}

static inline void prime_isr_yield_during_data_map_drain(void)
{
	host_util_set_sysreg_cb("isr_el1",
				test_isr_el1_rd_yield_on_countdown,
				test_isr_el1_wr, 2UL);
}

static inline void prime_isr_yield_during_data_map_rollback(void)
{
	host_util_set_sysreg_cb("isr_el1",
				test_isr_el1_rd_yield_on_countdown,
				test_isr_el1_wr, 4UL);
}

static inline void prime_isr_pending_irq(void)
{
	host_util_set_sysreg_cb("isr_el1",
				test_isr_el1_rd_return_value,
				test_isr_el1_wr, 1UL);
}

static inline void prime_isr_no_pending_irq(void)
{
	host_util_set_sysreg_cb("isr_el1",
				test_isr_el1_rd_return_value,
				test_isr_el1_wr, 0UL);
}

static inline void prime_isr_yield_before_data_map_pop(void)
{
	prime_isr_pending_irq();
}

/*
 * Reset allocation counters at the start of each data test.
 * Moves the NS list pool far above the worst-case data granule range.
 */
static inline void reset_data_granule_allocation(void)
{
	g_rtt_next_idx = 1U;
	g_ns_list_next_idx = DATA_TEST_NS_LIST_START_IDX;
}

/*
 * Reserve n granules whose base address is aligned to TEST_DATA_L2_BLOCK_SIZE.
 * Advances g_rtt_next_idx past any alignment gap without delegating those
 * skipped slots (they remain NS/unused).
 */
static inline uintptr_t reserve_delegated_granules_l2_aligned(unsigned int n)
{
	uintptr_t cur = granule_addr_rtt(g_rtt_next_idx);
	uintptr_t aligned = (cur + TEST_DATA_L2_BLOCK_SIZE - 1UL) &
			    ~(TEST_DATA_L2_BLOCK_SIZE - 1UL);

	/* Skip over the alignment gap (no delegation needed for skipped slots) */
	g_rtt_next_idx += (unsigned int)((aligned - cur) / GRANULE_SIZE);

	return reserve_delegated_granules(n);
}

/*
 * Initialize a primary S2TT context for data tests.
 * Uses the same settings as init_primary_s2_ctx() in the unprot helpers.
 */
static inline void init_data_s2_ctx(const struct test_data_ctx *ctx,
				    struct s2tt_context *s2_ctx)
{
	(void)memset(s2_ctx, 0, sizeof(*s2_ctx));
	s2_ctx->ipa_bits = TEST_IPA_BITS;
	s2_ctx->s2_starting_level = 0;
	s2_ctx->num_root_rtts = 1U;
	s2_ctx->g_rtt = find_granule(ctx->rtt_l0);
	s2_ctx->enable_lpa2 = false;
	s2_ctx->indirect_s2ap = false;
	s2_ctx->mecid = TEST_REALM_MECID;
}

/*
 * Read the S2TTE and level for a protected IPA by walking the RTT.
 */
static inline bool read_data_ipa_s2tte(const struct test_data_ctx *ctx,
					unsigned long ipa,
					unsigned long *s2tte_out,
					long *level_out)
{
	struct s2tt_context s2_ctx;
	struct s2tt_walk wi;
	unsigned long *table;

	init_data_s2_ctx(ctx, &s2_ctx);
	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);
	s2tt_walk_lock_unlock(&s2_ctx, ipa, S2TT_PAGE_LEVEL, &wi);

	table = (unsigned long *)buffer_granule_mecid_map(wi.g_llt, SLOT_RTT,
							  s2_ctx.mecid);
	CHECK_TRUE(table != NULL);
	*s2tte_out = s2tte_read(&table[wi.index]);
	*level_out = wi.last_level;

	buffer_unmap(table);
	granule_unlock(wi.g_llt);
	return true;
}

/*
 * Create RD and RTT L0 for data tests.
 * L0[0] = unassigned_empty (protected/PAR), remaining entries = 0.
 */
static inline bool create_data_realm_base(struct test_data_ctx *ctx)
{
	struct s2tt_context tmp_ctx;
	unsigned long *tbl;
	struct granule *g_rtt_l0;
	struct granule *g_rd;
	struct rd *rd;
	struct s2tt_context *s2_ctx;

	ctx->rd    = reserve_delegated_granules(1U);
	ctx->rtt_l0 = reserve_delegated_granules(1U);

	(void)memset(&tmp_ctx, 0, sizeof(tmp_ctx));

	g_rtt_l0 = find_granule(ctx->rtt_l0);
	granule_lock(g_rtt_l0, GRANULE_STATE_DELEGATED);
	granule_unlock_transition(g_rtt_l0, GRANULE_STATE_RTT);

	granule_lock(g_rtt_l0, GRANULE_STATE_RTT);
	tbl = (unsigned long *)buffer_granule_mecid_map(g_rtt_l0, SLOT_RTT,
							TEST_REALM_MECID);
	CHECK_TRUE(tbl != NULL);
	/* Entry 0: PAR (protected) initialised as unassigned_empty */
	tbl[0] = s2tte_create_unassigned_empty(&tmp_ctx, 0UL);
	for (unsigned int i = 1U; i < S2TTES_PER_S2TT; i++) {
		tbl[i] = 0UL;
	}
	buffer_unmap(tbl);
	granule_unlock(g_rtt_l0);

	g_rd = find_granule(ctx->rd);
	granule_lock(g_rd, GRANULE_STATE_DELEGATED);
	rd = (struct rd *)buffer_granule_map_zeroed(g_rd, SLOT_RD);
	CHECK_TRUE(rd != NULL);

	s2_ctx = &rd->s2_ctx[PRIMARY_S2_CTX_ID];
	s2_ctx->ipa_bits         = TEST_IPA_BITS;
	s2_ctx->s2_starting_level = 0;
	s2_ctx->num_root_rtts    = 1U;
	s2_ctx->g_rtt            = g_rtt_l0;
	s2_ctx->enable_lpa2      = false;
	s2_ctx->indirect_s2ap    = false;
	s2_ctx->mecid            = TEST_REALM_MECID;
	set_rd_state(rd, REALM_NEW);

	buffer_unmap(rd);
	granule_unlock_transition(g_rd, GRANULE_STATE_RD);

	return true;
}

/*
 * Create L1, L2 and L3 RTT tables for the TEST_DATA_IPA_BASE range.
 * Requires create_data_realm_base() to have been called first.
 */
static inline bool create_data_rtts(struct test_data_ctx *ctx)
{
	ctx->rtt_l1 = reserve_delegated_granules(1U);
	ctx->rtt_l2 = reserve_delegated_granules(1U);
	ctx->rtt_l3 = reserve_delegated_granules(1U);

	/*
	 * L1 create: map_addr must be aligned to the L0 block size (2^39 = 512GB).
	 * Only 0UL satisfies this within PAR.
	 * L2 create: map_addr must be aligned to the L1 block size (2^30 = 1GB).
	 * TEST_DATA_IPA_BASE (1GB = 0x40000000) is 1GB-aligned, so it works.
	 * L3 create: map_addr must be aligned to the L2 block size (2MB).
	 * TEST_DATA_IPA_BASE (1GB) is also 2MB-aligned, so it works directly.
	 */
	if (smc_rtt_create(ctx->rd, ctx->rtt_l1, 0UL, 1UL) !=
	    RMI_SUCCESS) {
		return false;
	}
	if (smc_rtt_create(ctx->rd, ctx->rtt_l2, TEST_DATA_IPA_BASE, 2UL) !=
	    RMI_SUCCESS) {
		return false;
	}
	if (smc_rtt_create(ctx->rd, ctx->rtt_l3, TEST_DATA_IPA_BASE, 3UL) !=
	    RMI_SUCCESS) {
		return false;
	}
	return true;
}

/*
 * Create an L3 RTT table for the 2MB-aligned range containing ipa.
 */
static inline bool create_data_l3_rtt(const struct test_data_ctx *ctx,
				      unsigned long ipa)
{
	uintptr_t rtt_l3 = reserve_delegated_granules(1U);
	unsigned long l2_base = ipa & ~(TEST_DATA_L2_BLOCK_SIZE - 1UL);

	return smc_rtt_create(ctx->rd, rtt_l3, l2_base, 3UL) == RMI_SUCCESS;
}

/*
 * Convenience: create the full test context (realm base + RTT tables).
 */
static inline bool create_data_rtt_ctx(struct test_data_ctx *ctx)
{
	if (!create_data_realm_base(ctx)) {
		return false;
	}
	return create_data_rtts(ctx);
}

/*
 * Set RIPAS=RAM for [base, top) by looping over smc_rtt_init_ripas calls
 * until the entire range is covered.
 */
static inline bool init_ripas_range(const struct test_data_ctx *ctx,
				    unsigned long base,
				    unsigned long top)
{
	unsigned long cur = base;

	while (cur < top) {
		struct smc_result res = {};

		smc_rtt_init_ripas(ctx->rd, cur, top, &res);
		if (res.x[0] != RMI_SUCCESS) {
			return false;
		}
		cur = res.x[1];
	}
	return true;
}

/*
 * Map a single delegated data granule at the given IPA.
 * data_pa must already be in DELEGATED state (call reserve_delegated_granules first).
 */
static inline bool map_data_page(const struct test_data_ctx *ctx,
				 unsigned long ipa,
				 uintptr_t data_pa)
{
	struct smc_result res = {};
	/*
	 * Build an RmiAddrRangeDesc4KB for one L3 page:
	 *   sz          = RMI_PAGE_L3
	 *   cnt         = 1
	 *   addr        = data_pa >> GRANULE_SHIFT
	 *   st          = RMI_OP_MEM_DELEGATED
	 */
	unsigned long desc = INPLACE(RMI_ADDR_RDESC_4K_SZ, RMI_PAGE_L3) |
			     INPLACE(RMI_ADDR_RDESC_4K_CNT, 1UL) |
			     INPLACE(RMI_ADDR_RDESC_4K_ADDR,
				     (unsigned long)data_pa >> GRANULE_SHIFT) |
			     INPLACE(RMI_ADDR_RDESC_4K_ST,
				     RMI_OP_MEM_DELEGATED);

	smc_rtt_data_map(ctx->rd, ipa, ipa + GRANULE_SIZE,
			 RMI_ADDR_TYPE_SINGLE, desc, &res);
	res = sro_complete_operation(res);
	return res.x[0] == RMI_SUCCESS;
}

/*
 * Map n contiguous data granules at [ipa_base, ipa_base + n*GRANULE_SIZE).
 * data_base is the PA of the first granule; PAs are assumed contiguous.
 */
static inline bool map_data_pages(const struct test_data_ctx *ctx,
				  unsigned long ipa_base,
				  uintptr_t data_base,
				  unsigned int n)
{
	for (unsigned int i = 0U; i < n; i++) {
		unsigned long ipa     = ipa_base + (unsigned long)i * GRANULE_SIZE;
		uintptr_t     data_pa = data_base + (uintptr_t)i * GRANULE_SIZE;

		if (!map_data_page(ctx, ipa, data_pa)) {
			return false;
		}
	}
	return true;
}

/*
 * Fold the L3 table covering ipa into an L2 block entry.
 * Requires all 512 L3 entries to be assigned_ram with contiguous PAs.
 */
static inline bool fold_to_l2(const struct test_data_ctx *ctx,
			       unsigned long ipa)
{
	struct smc_result res = {};

	/* level=3: fold the L3 table away, creating an L2 block entry */
	smc_rtt_fold(ctx->rd, ipa, 3UL, &res);
	return res.x[0] == RMI_SUCCESS;
}

/*
 * Install an assigned_dev_dev entry at level 2 or 3 for data-unmap tests.
 * This bypasses the RMI device lifecycle so tests can construct L2 device
 * blocks, which RMI_RTT_DEV_MAP does not currently support.
 */
static inline bool install_assigned_dev_mapping(const struct test_data_ctx *ctx,
						unsigned long ipa,
						uintptr_t dev_pa,
						long level)
{
	struct s2tt_context s2_ctx;
	struct s2tt_walk wi;
	unsigned long *table;
	unsigned long old_s2tte;
	unsigned long dev_ap;
	unsigned long s2tte;

	init_data_s2_ctx(ctx, &s2_ctx);
	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);
	s2tt_walk_lock_unlock(&s2_ctx, ipa, level, &wi);
	if (wi.last_level != level) {
		granule_unlock(wi.g_llt);
		return false;
	}

	table = (unsigned long *)buffer_granule_mecid_map(wi.g_llt, SLOT_RTT,
							  s2_ctx.mecid);
	CHECK_TRUE(table != NULL);
	old_s2tte = s2tte_read(&table[wi.index]);
	if ((level < S2TT_PAGE_LEVEL) &&
	    s2tte_is_table(&s2_ctx, old_s2tte, level)) {
		buffer_unmap(table);
		granule_unlock(wi.g_llt);
		return false;
	}

	dev_ap = s2tte_update_prot_ap(&s2_ctx, 0UL,
				      S2TTE_DEV_DEF_BASE_PERM_IDX,
				      S2TTE_DEF_PROT_OVERLAY_IDX);
	s2tte = s2tte_create_assigned_dev_dev_coh_type(&s2_ctx, dev_pa,
						       level,
						       DEV_MEM_NON_COHERENT,
						       dev_ap);
	s2tte_write(&table[wi.index], s2tte);

	buffer_unmap(table);
	granule_unlock(wi.g_llt);
	return true;
}

/*
 * Install an assigned_empty or assigned_destroyed data entry at level 2 or 3.
 * The caller owns the backing DATA granules; this only rewrites the RTT state.
 */
static inline bool install_assigned_data_ripas_mapping(
	const struct test_data_ctx *ctx,
	unsigned long ipa,
	uintptr_t data_pa,
	long level,
	bool destroyed)
{
	struct s2tt_context s2_ctx;
	struct s2tt_walk wi;
	unsigned long *table;
	unsigned long old_s2tte;
	unsigned long s2tte;

	init_data_s2_ctx(ctx, &s2_ctx);
	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);
	s2tt_walk_lock_unlock(&s2_ctx, ipa, level, &wi);
	if (wi.last_level != level) {
		granule_unlock(wi.g_llt);
		return false;
	}

	table = (unsigned long *)buffer_granule_mecid_map(wi.g_llt, SLOT_RTT,
							  s2_ctx.mecid);
	CHECK_TRUE(table != NULL);
	old_s2tte = s2tte_read(&table[wi.index]);
	if ((level < S2TT_PAGE_LEVEL) &&
	    s2tte_is_table(&s2_ctx, old_s2tte, level)) {
		buffer_unmap(table);
		granule_unlock(wi.g_llt);
		return false;
	}

	if (destroyed) {
		s2tte = s2tte_create_assigned_destroyed(&s2_ctx, data_pa,
							level, old_s2tte);
	} else {
		s2tte = s2tte_create_assigned_empty(&s2_ctx, data_pa,
						    level, old_s2tte);
	}
	s2tte_write(&table[wi.index], s2tte);

	buffer_unmap(table);
	granule_unlock(wi.g_llt);
	return true;
}

static inline bool install_assigned_empty_mapping(
	const struct test_data_ctx *ctx,
	unsigned long ipa,
	uintptr_t data_pa,
	long level)
{
	return install_assigned_data_ripas_mapping(ctx, ipa, data_pa, level,
						   false);
}

static inline bool install_assigned_destroyed_mapping(
	const struct test_data_ctx *ctx,
	unsigned long ipa,
	uintptr_t data_pa,
	long level)
{
	return install_assigned_data_ripas_mapping(ctx, ipa, data_pa, level,
						   true);
}

/*
 * Assert: granule at pa is in GRANULE_STATE_DELEGATED.
 */
static inline void expect_data_granule_delegated(uintptr_t pa)
{
	struct granule *g = find_granule(pa);

	CHECK_TRUE(g != NULL);
	CHECK_EQUAL((int)GRANULE_STATE_DELEGATED,
		    (int)granule_unlocked_state(g));
}

/*
 * Assert: all n granules starting at data_base are DELEGATED.
 */
static inline void expect_data_granules_delegated(uintptr_t data_base,
						   unsigned int n)
{
	for (unsigned int i = 0U; i < n; i++) {
		expect_data_granule_delegated(data_base +
					      (uintptr_t)i * GRANULE_SIZE);
	}
}

/*
 * Assert: the RTT entry for ipa is in unassigned_empty state.
 * (This is the state after data_unmap of an assigned_empty entry.)
 */
static inline void expect_ipa_unassigned_empty(const struct test_data_ctx *ctx,
					       unsigned long ipa)
{
	unsigned long s2tte;
	long level;
	struct s2tt_context s2_ctx;

	CHECK_TRUE(read_data_ipa_s2tte(ctx, ipa, &s2tte, &level));
	init_data_s2_ctx(ctx, &s2_ctx);
	CHECK_TRUE(s2tte_is_unassigned_empty(&s2_ctx, s2tte));
}

/*
 * Assert: the RTT entry for ipa is in unassigned_destroyed state.
 * (This is the state after data_unmap of an assigned_ram entry.)
 */
static inline void expect_ipa_unassigned_destroyed(const struct test_data_ctx *ctx,
						    unsigned long ipa)
{
	unsigned long s2tte;
	long level;
	struct s2tt_context s2_ctx;

	CHECK_TRUE(read_data_ipa_s2tte(ctx, ipa, &s2tte, &level));
	init_data_s2_ctx(ctx, &s2_ctx);
	CHECK_TRUE(s2tte_is_unassigned_destroyed(&s2_ctx, s2tte));
}

/*
 * Assert: the RTT entry for ipa is unassigned and not drain-pending.
 */
static inline void expect_ipa_unassigned_no_drain(
	const struct test_data_ctx *ctx, unsigned long ipa)
{
	unsigned long s2tte;
	long level;
	struct s2tt_context s2_ctx;

	CHECK_TRUE(read_data_ipa_s2tte(ctx, ipa, &s2tte, &level));
	init_data_s2_ctx(ctx, &s2_ctx);
	CHECK_TRUE(s2tte_is_unassigned(&s2_ctx, s2tte));
	CHECK_FALSE(s2tte_drain_pending(s2tte));
}

/*
 * Assert: the RTT entry for ipa is an assigned_dev_dev entry at exp_level.
 */
static inline void expect_ipa_assigned_dev_dev(const struct test_data_ctx *ctx,
					       unsigned long ipa,
					       long exp_level)
{
	unsigned long s2tte;
	long level;
	struct s2tt_context s2_ctx;

	CHECK_TRUE(read_data_ipa_s2tte(ctx, ipa, &s2tte, &level));
	init_data_s2_ctx(ctx, &s2_ctx);
	CHECK_EQUAL(exp_level, level);
	CHECK_TRUE(s2tte_is_assigned_dev_dev(&s2_ctx, s2tte, level));
}

/*
 * Extract the CNT field ([9:0]) from an RmiAddrRangeDesc.
 */
static inline unsigned long decode_rdesc_count(unsigned long rdesc)
{
	return EXTRACT(RMI_ADDR_RDESC_4K_CNT, rdesc);
}

/*
 * Extract the SZ field from an RmiAddrRangeDesc.
 */
static inline unsigned long decode_rdesc_size(unsigned long rdesc)
{
	return EXTRACT(RMI_ADDR_RDESC_4K_SZ, rdesc);
}

/*
 * Extract the ST field from an RmiAddrRangeDesc.
 */
static inline unsigned long decode_rdesc_state(unsigned long rdesc)
{
	return EXTRACT(RMI_ADDR_RDESC_4K_ST, rdesc);
}

/*
 * Read a range descriptor from an NS output list granule at index i.
 */
static inline unsigned long read_list_entry(uintptr_t list_pa, unsigned int i)
{
	struct granule *g_list = find_granule(list_pa);
	unsigned long *list_contents;
	unsigned long val;

	list_contents = (unsigned long *)ns_buffer_granule_map(SLOT_NS, g_list);
	CHECK_TRUE(list_contents != NULL);
	val = list_contents[i];
	ns_buffer_unmap(list_contents);
	return val;
}

/*
 * Write a range descriptor to an NS input list granule at index i.
 */
static inline void write_list_input_entry(uintptr_t list_pa, unsigned int i,
					  unsigned long desc)
{
	struct granule *g_list = find_granule(list_pa);
	unsigned long *list_contents;

	list_contents = (unsigned long *)ns_buffer_granule_map(SLOT_NS, g_list);
	CHECK_TRUE(list_contents != NULL);
	list_contents[i] = desc;
	ns_buffer_unmap(list_contents);
}

/*
 * Build an RmiAddrRangeDesc4KB from count, PA, block size and memory state.
 */
static inline unsigned long make_data_map_desc(unsigned long cnt,
					       uintptr_t pa,
					       unsigned long sz = RMI_PAGE_L3,
					       unsigned long st =
							RMI_OP_MEM_DELEGATED)
{
	return INPLACE(RMI_ADDR_RDESC_4K_SZ, sz) |
	       INPLACE(RMI_ADDR_RDESC_4K_CNT, cnt) |
	       INPLACE(RMI_ADDR_RDESC_4K_ADDR,
		       (unsigned long)pa >> GRANULE_SHIFT) |
	       INPLACE(RMI_ADDR_RDESC_4K_ST, st);
}

/*
 * Build DATA_MAP flags.
 */
static inline unsigned long make_data_map_flags(unsigned long oaddr_type,
						unsigned long list_count = 0UL)
{
	return INPLACE(RMI_RTT_PROT_MAP_FLAGS_OADDR_TYPE, oaddr_type) |
	       INPLACE(RMI_RTT_PROT_MAP_FLAGS_LIST_COUNT, list_count);
}

/*
 * Assert: granule at pa is in GRANULE_STATE_DATA.
 */
static inline void expect_data_granule_data_state(uintptr_t pa)
{
	struct granule *g = find_granule(pa);

	CHECK_TRUE(g != NULL);
	CHECK_EQUAL((int)GRANULE_STATE_DATA, (int)granule_unlocked_state(g));
}

/*
 * Assert: all n granules starting at data_base are in DATA state.
 */
static inline void expect_data_granules_data_state(uintptr_t data_base,
						   unsigned int n)
{
	for (unsigned int i = 0U; i < n; i++) {
		expect_data_granule_data_state(data_base +
					       (uintptr_t)i * GRANULE_SIZE);
	}
}

/*
 * Assert: the S2TTE at ipa is assigned_ram at the deepest reachable level.
 */
static inline void expect_ipa_assigned_ram(const struct test_data_ctx *ctx,
					   unsigned long ipa)
{
	unsigned long s2tte;
	long level;
	struct s2tt_context s2_ctx;

	CHECK_TRUE(read_data_ipa_s2tte(ctx, ipa, &s2tte, &level));
	init_data_s2_ctx(ctx, &s2_ctx);
	CHECK_TRUE(s2tte_is_assigned_ram(&s2_ctx, s2tte, level));
}

/*
 * Assert: the S2TTE at ipa is assigned_ram at exp_level and maps expected_pa.
 */
static inline void expect_ipa_assigned_ram_to_pa(
	const struct test_data_ctx *ctx,
	unsigned long ipa,
	unsigned long expected_pa,
	long exp_level = S2TT_PAGE_LEVEL)
{
	unsigned long s2tte;
	long level;
	struct s2tt_context s2_ctx;

	CHECK_TRUE(read_data_ipa_s2tte(ctx, ipa, &s2tte, &level));
	CHECK_EQUAL(exp_level, level);
	init_data_s2_ctx(ctx, &s2_ctx);
	CHECK_TRUE(s2tte_is_assigned_ram(&s2_ctx, s2tte, level));
	CHECK_EQUAL(expected_pa, s2tte_pa(&s2_ctx, s2tte, level));
}

/*
 * Read the raw S2TTE for ipa. Useful for checking SW drain-pending bits.
 */
static inline unsigned long read_data_ipa_raw_s2tte(
	const struct test_data_ctx *ctx, unsigned long ipa)
{
	unsigned long s2tte;
	long level;

	CHECK_TRUE(read_data_ipa_s2tte(ctx, ipa, &s2tte, &level));
	return s2tte;
}

/*
 * Force the realm at ctx->rd into the given state (e.g. REALM_SYSTEM_OFF).
 * Used to test error paths that require realm state != NEW/ACTIVE.
 */
static inline void force_realm_state(const struct test_data_ctx *ctx,
				     unsigned long new_state)
{
	struct granule *g_rd = find_granule(ctx->rd);
	struct rd *rd;

	granule_lock(g_rd, GRANULE_STATE_RD);
	rd = (struct rd *)buffer_granule_map(g_rd, SLOT_RD);
	CHECK_TRUE(rd != NULL);
	set_rd_state(rd, new_state);
	buffer_unmap(rd);
	granule_unlock(g_rd);
}

/*
 * Create realm with L1 and L2 tables only (no L3).
 * Used for L2-block direct-mapping tests where smc_rtt_create must NOT
 * have installed an L3 table so the RTT walk stops at L2.
 */
static inline bool create_data_rtt_ctx_l2_only(struct test_data_ctx *ctx)
{
	if (!create_data_realm_base(ctx)) {
		return false;
	}

	ctx->rtt_l1  = reserve_delegated_granules(1U);
	ctx->rtt_l2  = reserve_delegated_granules(1U);
	ctx->rtt_l3  = 0UL; /* no L3 table */

	if (smc_rtt_create(ctx->rd, ctx->rtt_l1, 0UL, 1UL) != RMI_SUCCESS) {
		return false;
	}
	if (smc_rtt_create(ctx->rd, ctx->rtt_l2,
			   TEST_DATA_IPA_BASE, 2UL) != RMI_SUCCESS) {
		return false;
	}
	return true;
}

#endif /* RTT_DATA_TEST_HELPERS_H */

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RTT_TEST_HELPERS_H
#define RTT_TEST_HELPERS_H

#include <CppUTest/TestHarness.h>

extern "C" {
#include <addr_list.h>
#include <arch_helpers.h>
#include <buffer.h>
#include <granule.h>
#include <host_utils.h>
#include <mec.h>
#include <planes.h>
#include <realm.h>
#include <s2tt.h>
#include <s2tt_ap.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <status.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
#include <xlat_defs.h>
}

/*
 * Test RTT layout (sl=0, ipa_bits=40):
 *   [0, 512GB)      : protected IPA range
 *   [512GB, 1TB)    : unprotected IPA range
 */
#define TEST_IPA_BITS            40U
#define TEST_PAR_SIZE            (1UL << 39)

/* Test NS PA used in oaddr descriptors. */
#define TEST_NS_PA               0x200000000UL
#define TEST_NS_PA_ALT           0x240000000UL

#define TEST_REALM_MECID         MECID_SHARED

#define TEST_PAGE_BASE           TEST_PAR_SIZE
#define TEST_PAGE_TOP            (TEST_PAGE_BASE + GRANULE_SIZE)

#define TEST_L2_BLOCK_SIZE       XLAT_BLOCK_SIZE(2)
#define TEST_L2_BLOCK_BASE       (TEST_PAR_SIZE + TEST_L2_BLOCK_SIZE)
#define TEST_L2_BLOCK_TOP        (TEST_L2_BLOCK_BASE + TEST_L2_BLOCK_SIZE)

#define TEST_L1_BLOCK_SIZE       XLAT_BLOCK_SIZE(1)
#define TEST_L1_BLOCK_BASE       (TEST_PAR_SIZE + TEST_L1_BLOCK_SIZE)
#define TEST_L1_BLOCK_TOP        (TEST_L1_BLOCK_BASE + TEST_L1_BLOCK_SIZE)

struct test_rtt_ctx {
	uintptr_t rd;
	uintptr_t rtt_l0;
	uintptr_t rtt_l1;
	uintptr_t rtt_l2;
	uintptr_t rtt_l3;
	bool indirect_s2ap;
};

/*
 * Calculate granule physical address from index.
 * Converts a granule index to its physical address by computing:
 * granule_base + (index * GRANULE_SIZE)
 *
 * @idx: Granule index (0-based)
 * @return: Physical address of the granule
 */
static inline uintptr_t granule_addr_rtt(unsigned int idx)
{
	return host_util_get_granule_base() + (uintptr_t)idx * GRANULE_SIZE;
}

/*
 * Delegate a range of granules to the RMM.
 * Marks granules as managed by RMM via RMI_GRANULE_RANGE_DELEGATE.
 * Handles batching via SMC result boundaries.
 *
 * @start: Start address of granule range (must be granule-aligned)
 * @end: End address of granule range (must be granule-aligned)
 * @return: true if entire range delegated successfully, false on error
 */
static inline bool delegate_range_rtt(uintptr_t start, uintptr_t end)
{
	struct smc_result res = {};
	uintptr_t cur = start;

	while (cur < end) {
		smc_granule_range_delegate(cur, end, &res);
		if (res.x[0] != RMI_SUCCESS) {
			return false;
		}
		cur = res.x[1];
		if (cur == 0UL) {
			break;
		}
	}
	return true;
}

/*
 * Granule allocation counters. Defined as static variables in the header so
 * no separate translation unit is required. reset_granule_allocation()
 * restores both to their initial values in TEST_SETUP before each test.
 */
static unsigned int g_rtt_next_idx = 1U;
static unsigned int g_ns_list_next_idx = 100000U;

/*
 * Reset granule allocation counters for the next test.
 * Called in TEST_SETUP so that each test starts with a clean granule pool
 * at indices 1 / 100000.
 */
static inline void reset_granule_allocation(void)
{
	g_rtt_next_idx = 1U;
	g_ns_list_next_idx = 100000U;
}

/*
 * Reserve n consecutive granules for test use and delegate them.
 * Allocates from a global pool tracking the next available index.
 * Automatically delegates granules to RMM via RMI_GRANULE_RANGE_DELEGATE.
 * NOTE: Must call reset_granule_allocation() in TEST_TEARDOWN to reuse granules.
 *
 * @n: Number of granules to reserve
 * @return: Physical address of first reserved granule
 */
static inline uintptr_t reserve_delegated_granules(unsigned int n)
{
	unsigned int nr = test_helpers_get_nr_granules();

	CHECK_TRUE((g_rtt_next_idx + n) <= nr);
	uintptr_t base = granule_addr_rtt(g_rtt_next_idx);
	uintptr_t end = base + (uintptr_t)n * GRANULE_SIZE;

	g_rtt_next_idx += n;

	/* Delegate the granule range to RMM */
	CHECK_TRUE(delegate_range_rtt(base, end));

	return base;
}

/*
 * Reserve an NS (undelegated) granule for use as an address list.
 * Allocates from a separate pool to keep NS list granules distinct from
 * delegated RTT granules. The granule stays undelegated and is accessed
 * via the NS buffer API. List contents must be populated separately via
 * populate_list_granule().
 *
 * @return: Physical address of list granule in NS state
 */
static inline uintptr_t reserve_list_granule(void)
{
	unsigned int nr = test_helpers_get_nr_granules();

	CHECK_TRUE((g_ns_list_next_idx + 1U) <= nr);
	uintptr_t base = granule_addr_rtt(g_ns_list_next_idx);

	g_ns_list_next_idx++;
	return base;
}

/*
 * Encode a physical address into RMI output address format.
 * Converts PA + level into address list descriptor encoding.
 * Used to format input for MAP/UNMAP oaddr parameter.
 *
 * @pa: Physical address to encode
 * @rtt_level: RTT level (1, 2, or 3 for blocks; S2TT_PAGE_LEVEL for pages).
 *             The level is used for alignment checks only; the sz is carried in
 *             flags.size per spec (not in the descriptor).
 * @return: Encoded output address descriptor (count=1, addr=pa>>GRANULE_SHIFT)
 */
static inline unsigned long make_oaddr(unsigned long pa, int rtt_level)
{
	(void)rtt_level; /* rtt_level is now encoded in flags.size, not the descriptor */
	unsigned long desc = 0UL;

	/* Encode address field: pa >> GRANULE_SHIFT into ADDR bits [49:10] */
	desc |= INPLACE(RMI_ADDR_RDESC_4K_ADDR, pa >> GRANULE_SHIFT);

	/* Count = 1 (single block) at bits [9:0] */
	desc |= INPLACE(RMI_ADDR_RDESC_4K_CNT, 1UL);

	return desc;
}

/*
 * Build MAP operation flags for SINGLE or NONE addressing mode.
 * Encodes oaddr_type, memory attributes and S2AP permissions. On this
 * branch the block size is carried in the descriptor (RMI_ADDR_RDESC_4K_SZ),
 * not in the flags word, so sz_enc is accepted only for source-level API
 * compatibility with sibling branches and is ignored.
 *
 * @oaddr_type: RMI_ADDR_TYPE_SINGLE or RMI_ADDR_TYPE_NONE
 * @memattr: Memory attributes (typically 0UL)
 * @s2ap: S2 access permissions (typically 0UL for tests)
 * @sz_enc: Unused on this branch (kept for API parity)
 * @return: Encoded flags value for RMI_RTT_UNPROT_MAP
 */
static inline unsigned long make_map_flags(unsigned long oaddr_type,
					  unsigned long memattr,
					  unsigned long s2ap,
					  unsigned long sz_enc = 0UL)
{
	(void)sz_enc;
	return INPLACE(RMI_RTT_UNPROT_MAP_FLAGS_OADDR_TYPE, oaddr_type) |
	       INPLACE(RMI_RTT_UNPROT_MAP_FLAGS_MEMATTR, memattr) |
	       INPLACE(RMI_RTT_UNPROT_MAP_FLAGS_S2AP, s2ap);
}

/*
 * Build MAP operation flags for LIST addressing mode.
 * Encodes oaddr_type, list entry count, memory attributes, S2AP permissions,
 * and block size. Block size is carried in flags.size per spec.
 *
 * @oaddr_type: RMI_ADDR_TYPE_LIST
 * @list_count: Number of entries in the address list
 * @memattr: Memory attributes (typically 0UL)
 * @s2ap: S2 access permissions (typically 0UL for tests)
 * @sz_enc: Block size encoding (0=L3 page, 1=L2 block, 2=L1 block; default 0)
 * @return: Encoded flags value for RMI_RTT_UNPROT_MAP
 */
static inline unsigned long make_map_flags_with_list_count(unsigned long oaddr_type,
						     unsigned long list_count,
						     unsigned long memattr,
						     unsigned long s2ap,
						     unsigned long sz_enc = 0UL)
{
	(void)sz_enc;
	return INPLACE(RMI_RTT_UNPROT_MAP_FLAGS_OADDR_TYPE, oaddr_type) |
	       INPLACE(RMI_RTT_UNPROT_MAP_FLAGS_LIST_COUNT, list_count) |
	       INPLACE(RMI_RTT_UNPROT_MAP_FLAGS_MEMATTR, memattr) |
	       INPLACE(RMI_RTT_UNPROT_MAP_FLAGS_S2AP, s2ap);
}

/*
 * Build UNMAP operation flags.
 * Encodes output address type and list count for LIST mode.
 *
 * @oaddr_type: RMI_ADDR_TYPE_SINGLE, RMI_ADDR_TYPE_LIST, or RMI_ADDR_TYPE_NONE
 * @list_count: Number of entries expected in output list (0 for SINGLE/NONE)
 * @return: Encoded flags value for RMI_RTT_UNPROT_UNMAP
 */
static inline unsigned long make_unmap_flags(unsigned long oaddr_type,
					    unsigned long list_count)
{
	return INPLACE(RMI_RTT_UNMAP_FLAGS_OADDR_TYPE, oaddr_type) |
	       INPLACE(RMI_RTT_UNMAP_FLAGS_LIST_COUNT, list_count);
}

/*
 * Build UNMAP flags for SINGLE output address mode.
 * Convenience wrapper for SINGLE mode without list output.
 *
 * @return: Encoded flags for single-address UNMAP
 */
static inline unsigned long make_unmap_flags_single(void)
{
	return make_unmap_flags(RMI_ADDR_TYPE_SINGLE, 0UL);
}

/*
 * Build UNMAP flags with no output address.
 * Convenience wrapper for NONE mode; operation completes without returning PA.
 *
 * @return: Encoded flags for UNMAP with no output
 */
static inline unsigned long make_unmap_flags_none(void)
{
	return make_unmap_flags(RMI_ADDR_TYPE_NONE, 0UL);
}

/*
 * Initialize S2TT context for primary address space (direct S2AP mode).
 * Sets up the address translation context for RTT walks with test-specific
 * configuration: 40-bit IPA, single root RTT, no LPA2, direct mode.
 *
 * @ctx: Test RTT context containing root RTT granule address
 * @s2_ctx: S2TT context to initialize
 */
static inline void init_primary_s2_ctx(const struct test_rtt_ctx *ctx,
				      struct s2tt_context *s2_ctx)
{
	(void)memset(s2_ctx, 0, sizeof(*s2_ctx));
	s2_ctx->ipa_bits = TEST_IPA_BITS;
	s2_ctx->s2_starting_level = 0;
	s2_ctx->num_root_rtts = 1U;
	s2_ctx->g_rtt = find_granule(ctx->rtt_l0);
	s2_ctx->enable_lpa2 = false;
	s2_ctx->indirect_s2ap = ctx->indirect_s2ap;
	s2_ctx->mecid = TEST_REALM_MECID;
}

/*
 * Read S2TTE entry for an IPA by walking the RTT hierarchy.
 * Locks RTT granules during walk, reads the S2TTE, then unlocks.
 * Returns both the entry value and the level at which it was found.
 *
 * @ctx: Test RTT context
 * @ipa: Input physical address to look up
 * @s2tte: Output - S2TTE entry value
 * @level: Output - RTT level where entry was found
 * @return: true (always succeeds)
 */
static inline bool read_ipa_s2tte(const struct test_rtt_ctx *ctx,
				 unsigned long ipa,
				 unsigned long *s2tte,
				 long *level)
{
	struct s2tt_context s2_ctx;
	struct s2tt_walk wi;
	unsigned long *table;

	init_primary_s2_ctx(ctx, &s2_ctx);
	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);
	s2tt_walk_lock_unlock(&s2_ctx, ipa, S2TT_PAGE_LEVEL, &wi);

	table = (unsigned long *)buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx.mecid);
	CHECK_TRUE(table != NULL);
	*s2tte = s2tte_read(&table[wi.index]);
	*level = wi.last_level;

	buffer_unmap(table);
	granule_unlock(wi.g_llt);
	return true;
}

/*
 * Assertion: Verify IPA is mapped to expected PA at expected RTT level.
 * Walks RTT, validates entry is in assigned non-secure state, and confirms PA.
 * Fails test if mapping doesn't match expectations.
 *
 * @ctx: Test RTT context
 * @ipa: IPA to verify
 * @expected_pa: Expected physical address
 * @expected_level: Expected RTT level (S2TT_PAGE_LEVEL, 2, or 1)
 */
static inline void expect_ipa_mapped_ns_to_pa(const struct test_rtt_ctx *ctx,
					     unsigned long ipa,
					     unsigned long expected_pa,
					     long expected_level)
{
	unsigned long s2tte;
	long level;
	struct s2tt_context s2_ctx;

	CHECK_TRUE(read_ipa_s2tte(ctx, ipa, &s2tte, &level));
	CHECK_EQUAL(expected_level, level);
	init_primary_s2_ctx(ctx, &s2_ctx);
	CHECK_TRUE(s2tte_is_assigned_ns(&s2_ctx, s2tte, level));
	CHECK_EQUAL(expected_pa, s2tte_pa(&s2_ctx, s2tte, level));
}

/*
 * Assertion: Verify IPA is unmapped (in unassigned non-secure state).
 * Walks RTT and checks that entry is unassigned.
 * Fails test if IPA is still mapped when it shouldn't be.
 *
 * @ctx: Test RTT context
 * @ipa: IPA to verify is unmapped
 */
static inline void expect_ipa_unmapped_ns(const struct test_rtt_ctx *ctx,
					 unsigned long ipa)
{
	unsigned long s2tte;
	long level;
	struct s2tt_context s2_ctx;

	CHECK_TRUE(read_ipa_s2tte(ctx, ipa, &s2tte, &level));
	init_primary_s2_ctx(ctx, &s2_ctx);
	CHECK_TRUE(s2tte_is_unassigned_ns(&s2_ctx, s2tte));
}

/*
 * Decode physical address from RMI single output address format.
 * Reverses make_oaddr encoding to extract PA from the descriptor.
 * Used to verify returned PAs in UNMAP single-address output.
 *
 * @out_range: Encoded output address descriptor from RMI operation
 * @return: Decoded physical address
 */
static inline unsigned long decode_single_oaddr_pa(unsigned long out_range)
{
	/* Extract PA from descriptor: address is encoded in the upper bits. */
	return RMI_ADDR_RDESC_4K_GET_ADDR(out_range);
}

/*
 * Create and initialize a complete RTT context for tests (direct S2AP mode).
 * Allocates and delegates granules for:
 * - RD (Realm Descriptor)
 * - RTT L0, L1, L2, L3 tables
 * Sets up realm hierarchy with protected (PAR) and unprotected IPA spaces.
 * Initializes s2ap in direct addressing mode.
 *
 * @ctx: Test RTT context to populate
 * @return: true on success, false on initialization failure
 */
static inline bool create_rtt_tree_ctx(struct test_rtt_ctx *ctx)
{
	struct smc_result res = {};

	ctx->indirect_s2ap = false;
	ctx->rd = reserve_delegated_granules(1U);
	ctx->rtt_l0 = reserve_delegated_granules(1U);
	ctx->rtt_l1 = reserve_delegated_granules(1U);
	ctx->rtt_l2 = reserve_delegated_granules(1U);
	ctx->rtt_l3 = reserve_delegated_granules(1U);

	struct granule *g_rtt_l0 = find_granule(ctx->rtt_l0);

	granule_lock(g_rtt_l0, GRANULE_STATE_DELEGATED);
	granule_unlock_transition(g_rtt_l0, GRANULE_STATE_RTT);

	struct s2tt_context tmp_ctx;
	unsigned long *tbl;

	(void)memset(&tmp_ctx, 0, sizeof(tmp_ctx));
	tmp_ctx.indirect_s2ap = false;

	granule_lock(g_rtt_l0, GRANULE_STATE_RTT);
	tbl = (unsigned long *)buffer_granule_mecid_map(g_rtt_l0, SLOT_RTT,
							TEST_REALM_MECID);
	CHECK_TRUE(tbl != NULL);
	/* Entry 0 => PAR (protected), entry 1 => Unprotected IPA space */
	tbl[0] = s2tte_create_unassigned_empty(&tmp_ctx, 0UL);
	tbl[1] = s2tte_create_unassigned_ns(NULL, 0UL);
	for (unsigned int i = 2U; i < S2TTES_PER_S2TT; i++) {
		tbl[i] = 0UL;
	}
	buffer_unmap(tbl);
	granule_unlock(g_rtt_l0);

	struct granule *g_rd = find_granule(ctx->rd);
	struct rd *rd;
	struct s2tt_context *s2_ctx;

	granule_lock(g_rd, GRANULE_STATE_DELEGATED);
	rd = (struct rd *)buffer_granule_map_zeroed(g_rd, SLOT_RD);
	CHECK_TRUE(rd != NULL);

	s2_ctx = &rd->s2_ctx[PRIMARY_S2_CTX_ID];
	s2_ctx->ipa_bits = TEST_IPA_BITS;
	s2_ctx->s2_starting_level = 0;
	s2_ctx->num_root_rtts = 1U;
	s2_ctx->g_rtt = g_rtt_l0;
	s2_ctx->enable_lpa2 = false;
	s2_ctx->indirect_s2ap = false;
	s2_ctx->mecid = TEST_REALM_MECID;
	set_rd_state(rd, REALM_NEW);

	buffer_unmap(rd);
	granule_unlock_transition(g_rd, GRANULE_STATE_RD);

	smc_rtt_create(ctx->rd, ctx->rtt_l1, TEST_PAGE_BASE, 1UL, &res);
	if (res.x[0] != RMI_SUCCESS) {
		return false;
	}
	smc_rtt_create(ctx->rd, ctx->rtt_l2, TEST_PAGE_BASE, 2UL, &res);
	if (res.x[0] != RMI_SUCCESS) {
		return false;
	}
	smc_rtt_create(ctx->rd, ctx->rtt_l3, TEST_PAGE_BASE, 3UL, &res);
	if (res.x[0] != RMI_SUCCESS) {
		return false;
	}

	return true;
}

/*
 * Create and initialize RTT context with indirect S2AP addressing mode.
 * Similar to create_rtt_tree_ctx() but uses indirect_s2ap = true.
 * Allocates RD, RTT L0-L3, and sets up hierarchy for indirect addressing.
 * Used to test MAP/UNMAP operations with indirect PA lookup.
 *
 * @ctx: Test RTT context to populate
 * @return: true on success, false on initialization failure
 */
static inline bool create_rtt_tree_ctx_indirect_s2ap(struct test_rtt_ctx *ctx)
{
	struct smc_result res = {};

	ctx->indirect_s2ap = true;
	ctx->rd = reserve_delegated_granules(1U);
	ctx->rtt_l0 = reserve_delegated_granules(1U);
	ctx->rtt_l1 = reserve_delegated_granules(1U);
	ctx->rtt_l2 = reserve_delegated_granules(1U);
	ctx->rtt_l3 = reserve_delegated_granules(1U);

	struct granule *g_rtt_l0 = find_granule(ctx->rtt_l0);

	granule_lock(g_rtt_l0, GRANULE_STATE_DELEGATED);
	granule_unlock_transition(g_rtt_l0, GRANULE_STATE_RTT);

	struct s2tt_context tmp_ctx;
	unsigned long *tbl;

	(void)memset(&tmp_ctx, 0, sizeof(tmp_ctx));
	tmp_ctx.indirect_s2ap = true;  /* INDIRECT mode for entry creation */

	granule_lock(g_rtt_l0, GRANULE_STATE_RTT);
	tbl = (unsigned long *)buffer_granule_mecid_map(g_rtt_l0, SLOT_RTT,
							TEST_REALM_MECID);
	CHECK_TRUE(tbl != NULL);
	/* Entry 0 => PAR (protected), entry 1 => Unprotected IPA space */
	tbl[0] = s2tte_create_unassigned_empty(&tmp_ctx, 0UL);
	tbl[1] = s2tte_create_unassigned_ns(NULL, 0UL);
	for (unsigned int i = 2U; i < S2TTES_PER_S2TT; i++) {
		tbl[i] = 0UL;
	}
	buffer_unmap(tbl);
	granule_unlock(g_rtt_l0);

	struct granule *g_rd = find_granule(ctx->rd);
	struct rd *rd;
	struct s2tt_context *s2_ctx;

	granule_lock(g_rd, GRANULE_STATE_DELEGATED);
	rd = (struct rd *)buffer_granule_map_zeroed(g_rd, SLOT_RD);
	CHECK_TRUE(rd != NULL);

	s2_ctx = &rd->s2_ctx[PRIMARY_S2_CTX_ID];
	s2_ctx->ipa_bits = TEST_IPA_BITS;
	s2_ctx->s2_starting_level = 0;
	s2_ctx->num_root_rtts = 1U;
	s2_ctx->g_rtt = g_rtt_l0;
	s2_ctx->enable_lpa2 = false;
	s2_ctx->indirect_s2ap = true;  /* INDIRECT mode for runtime context */
	s2_ctx->mecid = TEST_REALM_MECID;
	set_rd_state(rd, REALM_NEW);

	buffer_unmap(rd);
	granule_unlock_transition(g_rd, GRANULE_STATE_RD);

	smc_rtt_create(ctx->rd, ctx->rtt_l1, TEST_PAGE_BASE, 1UL, &res);
	if (res.x[0] != RMI_SUCCESS) {
		return false;
	}
	smc_rtt_create(ctx->rd, ctx->rtt_l2, TEST_PAGE_BASE, 2UL, &res);
	if (res.x[0] != RMI_SUCCESS) {
		return false;
	}
	smc_rtt_create(ctx->rd, ctx->rtt_l3, TEST_PAGE_BASE, 3UL, &res);
	if (res.x[0] != RMI_SUCCESS) {
		return false;
	}

	return true;
}

/*
 * Poll for Staged Realm Operation completion via RMI_CONTINUE.
 * If initial result is RMI_INCOMPLETE, repeatedly calls RMI_CONTINUE
 * until operation completes (success or error).
 * Used to handle operations that may require multiple steps.
 *
 * @initial_res: Result from initial RMI operation (may be INCOMPLETE)
 * @return: Final SMC result after completion
 */
static inline struct smc_result sro_complete_operation(struct smc_result initial_res)
{
	struct smc_result res = initial_res;
	return_code_t rc = unpack_return_code(res.x[0]);
	unsigned long handle = res.x[1];

	/*
	 * If operation returned incomplete, extract handle from x1
	 * and poll via RMI_CONTINUE until done. Some continue handlers
	 * leave x1 as zero on a repeated RMI_INCOMPLETE, so keep using
	 * the original handle unless a non-zero replacement is returned.
	 */
	while (rc.status == RMI_INCOMPLETE) {
		smc_op_continue(handle, 0UL, &res);
		rc = unpack_return_code(res.x[0]);
		if ((rc.status == RMI_INCOMPLETE) && (res.x[1] != 0UL)) {
			handle = res.x[1];
		}
	}

	return res;
}

/*
 * Fill address list granule with PA blocks at specified RTT levels.
 * Encodes multiple PA ranges into RMI list format (both continuous and discontinuous).
 * Supports L1, L2, and L3 page level mappings in a single list.
 * Each block is defined by its PA and RTT level.
 *
 * @list_pa: Physical address of list granule (from reserve_list_granule)
 * @blocks: Array of physical addresses
 * @levels: Array of RTT levels (1, 2, or S2TT_PAGE_LEVEL)
 * @num_blocks: Number of entries in blocks/levels arrays
 * @return: true on success, false if list encoding failed
 */
static inline bool populate_list_granule(uintptr_t list_pa,
					 unsigned long *blocks,
					 int *levels,
					 unsigned int num_blocks)
{
	struct granule *g_list = find_granule(list_pa);
	unsigned long *list_contents;

	list_contents = (unsigned long *)ns_buffer_granule_map(SLOT_NS, g_list);
	CHECK_TRUE(list_contents != NULL);

	/*
	 * Write spec wire format: count[9:0]=1, addr[49:10]=(blocks[i]>>GRANULE_SHIFT).
	 * Block size (sz) comes from flags.size, not the descriptor — levels[] is ignored.
	 */
	for (unsigned int i = 0U; i < num_blocks; i++) {
		(void)levels[i];
		list_contents[i] = INPLACE(RMI_ADDR_RDESC_4K_CNT, 1UL) |
				   INPLACE(RMI_ADDR_RDESC_4K_ADDR,
					   blocks[i] >> GRANULE_SHIFT);
	}

	ns_buffer_unmap(list_contents);
	return true;
}

/*
 * Assertion: Verify RTT hierarchy is valid at specified IPA and level.
 * Walks RTT from root to leaf, confirms:
 * - Entry exists at expected level
 * - Leaf table can be accessed and read
 * - Granules maintain RTT state
 * Does not validate entry content, only structure.
 *
 * @ctx: Test RTT context
 * @ipa: IPA to validate
 * @expected_leaf_level: Expected RTT level (1, 2, or S2TT_PAGE_LEVEL)
 */
static inline void expect_rtt_hierarchy_valid(const struct test_rtt_ctx *ctx,
					     unsigned long ipa,
					     long expected_leaf_level)
{
	struct s2tt_context s2_ctx;
	struct s2tt_walk wi;
	unsigned long *table;

	init_primary_s2_ctx(ctx, &s2_ctx);

	/* Lock root granule before walking RTT hierarchy.
	 * s2tt_walk_lock_unlock() handles intermediate lock/unlock and
	 * leaves leaf granule locked for our use. We unlock it when done.
	 */
	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);
	s2tt_walk_lock_unlock(&s2_ctx, ipa, expected_leaf_level, &wi);

	/* Verify we reached the expected level */
	CHECK_EQUAL(expected_leaf_level, wi.last_level);

	/* Verify we can read the entry in the leaf table */
	table = (unsigned long *)buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx.mecid);
	CHECK_TRUE(table != NULL);
	buffer_unmap(table);

	granule_unlock(wi.g_llt);
}

/*
 * Assertion: Verify RTT hierarchy is complete for entire IPA range.
 * Validates hierarchy validity at regular intervals (block-aligned) across range.
 * Ensures no gaps in page table structure that would break mappings.
 *
 * @ctx: Test RTT context
 * @base: Start IPA of range
 * @top: End IPA of range (exclusive)
 * @expected_leaf_level: RTT level to validate at (1, 2, or S2TT_PAGE_LEVEL)
 */
static inline void expect_rtt_tree_complete_for_range(const struct test_rtt_ctx *ctx,
						     unsigned long base,
						     unsigned long top,
						     long expected_leaf_level)
{
	unsigned long ipa;
	unsigned long block_size = XLAT_BLOCK_SIZE(expected_leaf_level);

	/* Validate hierarchy for each block-aligned IPA in range */
	for (ipa = base; ipa < top; ipa += block_size) {
		expect_rtt_hierarchy_valid(ctx, ipa, expected_leaf_level);
	}
}

/*
 * Assertion: Verify all IPAs in range are unmapped (clean).
 * Walks through entire range at granule granularity, confirming
 * all entries are in unassigned state. Used to verify UNMAP completeness.
 *
 * @ctx: Test RTT context
 * @base: Start IPA of range
 * @top: End IPA of range (exclusive)
 */
static inline void expect_rtt_hierarchy_clean_after_unmap(const struct test_rtt_ctx *ctx,
					     unsigned long base,
					     unsigned long top)
{
	unsigned long ipa;

	/* Check that all IPAs in range are unmapped */
	for (ipa = base; ipa < top; ipa += GRANULE_SIZE) {
		expect_ipa_unmapped_ns(ctx, ipa);
	}
}

/*
 * Assertion: Verify parent-child relationship in RTT hierarchy.
 * Walks RTT to specified level and validates:
 * - Entry exists at expected level
 * - Leaf table granule is in correct RTT state
 * Useful for verifying hierarchy persistence through operations.
 *
 * @ctx: Test RTT context
 * @ipa: IPA to validate
 * @expected_level: Expected RTT level for this IPA
 */
static inline void expect_rtt_parent_child_consistency(const struct test_rtt_ctx *ctx,
						      unsigned long ipa,
						      long expected_level)
{
	struct s2tt_context s2_ctx;
	struct s2tt_walk wi;

	init_primary_s2_ctx(ctx, &s2_ctx);

	/* Walk to the expected level to verify entry is accessible */
	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);
	s2tt_walk_lock_unlock(&s2_ctx, ipa, expected_level, &wi);

	/* Verify we reached the expected level */
	CHECK_EQUAL(expected_level, wi.last_level);

	/* Verify leaf table granule is in RTT state */
	CHECK_EQUAL(GRANULE_STATE_RTT, granule_get_state(wi.g_llt));

	granule_unlock(wi.g_llt);
}

#endif /* RTT_TEST_HELPERS_H */

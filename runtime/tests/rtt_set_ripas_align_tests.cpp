/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <rec.h>
}

#include "rtt_data_test_helpers.h"

/*
 * RMI_RTT_SET_RIPAS base_align with an already matching RIPAS.
 *
 * DEN0137 2.0-bet3 B4.5.71.2 base_align is
 *
 *   pre: (!AddrIsRttLevelAligned(base, walk.level)
 *         && ripas_pre != rec.ripas_value)
 *
 * so a base that is not aligned to the level at which the RTT walk
 * terminates is only rejected when the entry's RIPAS differs from the
 * value the Realm requested. When it already matches, no other failure
 * pre-condition holds and RVHFHD requires success.
 *
 * The tests build a Realm whose protected IPA space is mapped down to
 * level 2 only, so a 4KB request inside the first 2MB block terminates the
 * walk at level 2 even when it starts at the block's base. The REC carries
 * the pending request that handle_rsi_ipa_state_set() records; the entry's
 * RIPAS is EMPTY as left by RMI_RTT_CREATE.
 */

#define SET_RIPAS_ALIGN_TEST_RTT_START_IDX	114000U
#define SET_RIPAS_ALIGN_TEST_NS_LIST_START_IDX	127200U

#define SET_RIPAS_ALIGN_TEST_BASE	(TEST_DATA_IPA_BASE + GRANULE_SIZE)
#define SET_RIPAS_ALIGN_TEST_TOP	(SET_RIPAS_ALIGN_TEST_BASE + GRANULE_SIZE)

TEST_GROUP(rtt_set_ripas_align_tests) {
	TEST_SETUP()
	{
		static bool counters_initialized;

		if (!counters_initialized) {
			reset_data_granule_allocation();
			g_rtt_next_idx = SET_RIPAS_ALIGN_TEST_RTT_START_IDX;
			g_ns_list_next_idx = SET_RIPAS_ALIGN_TEST_NS_LIST_START_IDX;
			counters_initialized = true;
		}
		test_helpers_init();
		test_helpers_rmm_start(false);
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
	}

	TEST_TEARDOWN()
	{
	}
};

/* Realm base plus level 1 and level 2 RTTs for TEST_DATA_IPA_BASE. */
static void create_realm_to_level2(struct test_data_ctx *ctx)
{
	struct smc_result res = {};

	CHECK_TRUE(create_data_realm_base(ctx));
	ctx->rtt_l1 = reserve_delegated_granules(1U);
	ctx->rtt_l2 = reserve_delegated_granules(1U);
	ctx->rtt_l3 = 0UL;

	smc_rtt_create(ctx->rd, ctx->rtt_l1, 0UL, 1UL, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	smc_rtt_create(ctx->rd, ctx->rtt_l2, TEST_DATA_IPA_BASE, 2UL, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
}

/*
 * Create a REC granule bound to the Realm carrying the pending RIPAS
 * change request that handle_rsi_ipa_state_set() records.
 */
static uintptr_t create_requesting_rec(const struct test_data_ctx *ctx,
				       unsigned long base, unsigned long top,
				       enum ripas ripas_val)
{
	uintptr_t rec_pa = reserve_delegated_granules(1U);
	struct granule *g_rec = tr_find_fine_granule(rec_pa);
	struct rec *rec;

	granule_lock(g_rec, GRANULE_STATE_DELEGATED);
	rec = (struct rec *)buffer_granule_map_zeroed(g_rec, SLOT_REC);
	CHECK_TRUE(rec != NULL);

	rec->g_rec = g_rec;
	rec->realm_info.g_rd = tr_find_fine_granule(ctx->rd);
	rec->set_ripas.base = base;
	rec->set_ripas.top = top;
	rec->set_ripas.addr = base;
	rec->set_ripas.ripas_val = ripas_val;
	rec->set_ripas.change_destroyed = NO_CHANGE_DESTROYED;

	buffer_unmap(rec);
	granule_unlock_transition(g_rec, GRANULE_STATE_REC);
	return rec_pa;
}

static unsigned long rec_next_addr(uintptr_t rec_pa)
{
	struct granule *g_rec = tr_find_fine_granule(rec_pa);
	struct rec *rec;
	unsigned long addr;

	granule_lock(g_rec, GRANULE_STATE_REC);
	rec = (struct rec *)buffer_granule_map(g_rec, SLOT_REC);
	CHECK_TRUE(rec != NULL);
	addr = rec->set_ripas.addr;
	buffer_unmap(rec);
	granule_unlock(g_rec);
	return addr;
}

static void expect_entry_ripas(const struct test_data_ctx *ctx,
			       unsigned long ipa, unsigned long ripas)
{
	struct smc_result res = {};

	smc_rtt_read_entry(ctx->rd, ipa, S2TT_PAGE_LEVEL, &res);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(2UL, res.x[1]);
	UNSIGNED_LONGS_EQUAL(ripas, res.x[4]);
}

/* Control: an unaligned base with a different RIPAS is rejected. */
TEST(rtt_set_ripas_align_tests, unaligned_base_different_ripas_fails)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t rec_pa;

	create_realm_to_level2(&ctx);
	rec_pa = create_requesting_rec(&ctx, SET_RIPAS_ALIGN_TEST_BASE,
				       SET_RIPAS_ALIGN_TEST_TOP, RIPAS_RAM);

	smc_rtt_set_ripas(ctx.rd, rec_pa, SET_RIPAS_ALIGN_TEST_BASE,
			  SET_RIPAS_ALIGN_TEST_TOP, &res);

	UNSIGNED_LONGS_EQUAL(pack_return_code_level(RMI_ERROR_RTT,
						    (unsigned char)2U),
			     res.x[0]);
	UNSIGNED_LONGS_EQUAL(SET_RIPAS_ALIGN_TEST_BASE, rec_next_addr(rec_pa));
	expect_entry_ripas(&ctx, TEST_DATA_IPA_BASE, (unsigned long)RIPAS_EMPTY);
}

/* Control: an aligned request changes the level 2 entry. */
TEST(rtt_set_ripas_align_tests, aligned_base_changes_ripas)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t rec_pa;

	create_realm_to_level2(&ctx);
	rec_pa = create_requesting_rec(&ctx, TEST_DATA_IPA_BASE,
				       TEST_DATA_L2_BLOCK_TOP, RIPAS_RAM);

	smc_rtt_set_ripas(ctx.rd, rec_pa, TEST_DATA_IPA_BASE,
			  TEST_DATA_L2_BLOCK_TOP, &res);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(TEST_DATA_L2_BLOCK_TOP, res.x[1]);
	UNSIGNED_LONGS_EQUAL(TEST_DATA_L2_BLOCK_TOP, rec_next_addr(rec_pa));
	expect_entry_ripas(&ctx, TEST_DATA_IPA_BASE, (unsigned long)RIPAS_RAM);
}

/*
 * A request starting at an aligned base can end inside an entry whose RIPAS
 * already matches. The whole requested range is complete without unfolding.
 */
TEST(rtt_set_ripas_align_tests, aligned_base_matching_ripas_succeeds)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t rec_pa;

	create_realm_to_level2(&ctx);
	rec_pa = create_requesting_rec(&ctx, TEST_DATA_IPA_BASE,
				       TEST_DATA_PAGE_TOP, RIPAS_EMPTY);

	smc_rtt_set_ripas(ctx.rd, rec_pa, TEST_DATA_IPA_BASE,
			  TEST_DATA_PAGE_TOP, &res);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(TEST_DATA_PAGE_TOP, res.x[1]);
	UNSIGNED_LONGS_EQUAL(TEST_DATA_PAGE_TOP, rec_next_addr(rec_pa));
	expect_entry_ripas(&ctx, TEST_DATA_IPA_BASE, (unsigned long)RIPAS_EMPTY);
}

/* A partial level 2 entry cannot be changed to a different RIPAS. */
TEST(rtt_set_ripas_align_tests, aligned_base_different_ripas_fails)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t rec_pa;

	create_realm_to_level2(&ctx);
	rec_pa = create_requesting_rec(&ctx, TEST_DATA_IPA_BASE,
				       TEST_DATA_PAGE_TOP, RIPAS_RAM);

	smc_rtt_set_ripas(ctx.rd, rec_pa, TEST_DATA_IPA_BASE,
			  TEST_DATA_PAGE_TOP, &res);

	UNSIGNED_LONGS_EQUAL(pack_return_code_level(RMI_ERROR_RTT,
						    (unsigned char)2U),
			     res.x[0]);
	UNSIGNED_LONGS_EQUAL(TEST_DATA_IPA_BASE, rec_next_addr(rec_pa));
	expect_entry_ripas(&ctx, TEST_DATA_IPA_BASE, (unsigned long)RIPAS_EMPTY);
}

/*
 * B4.5.71.2 base_align + RVHFHD: an unaligned base whose entry already has
 * the requested RIPAS succeeds; the request is complete up to the top of
 * the request (which lies inside the entry) and the entry is untouched.
 */
TEST(rtt_set_ripas_align_tests, unaligned_base_matching_ripas_succeeds)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t rec_pa;

	create_realm_to_level2(&ctx);
	rec_pa = create_requesting_rec(&ctx, SET_RIPAS_ALIGN_TEST_BASE,
				       SET_RIPAS_ALIGN_TEST_TOP, RIPAS_EMPTY);

	smc_rtt_set_ripas(ctx.rd, rec_pa, SET_RIPAS_ALIGN_TEST_BASE,
			  SET_RIPAS_ALIGN_TEST_TOP, &res);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(SET_RIPAS_ALIGN_TEST_TOP, res.x[1]);
	UNSIGNED_LONGS_EQUAL(SET_RIPAS_ALIGN_TEST_TOP, rec_next_addr(rec_pa));
	expect_entry_ripas(&ctx, TEST_DATA_IPA_BASE, (unsigned long)RIPAS_EMPTY);
}

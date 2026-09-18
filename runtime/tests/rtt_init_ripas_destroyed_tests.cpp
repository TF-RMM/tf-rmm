/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

#include "rtt_data_test_helpers.h"

/*
 * RMI_RTT_INIT_RIPAS over entries whose RIPAS is DESTROYED.
 *
 * DEN0137 2.0-bet3 B4.5.69: the walk covers every entry whose state is
 * RTTE_VOID or RTTE_DATA (walk_top, B3.208), the entries in
 * [base, walk_top) get RIPAS_RAM (rtte_ripas) and out_top == walk_top.
 * RIPAS is not part of the RTTE state, so an entry left with
 * RIPAS_DESTROYED by RMI_RTT_DATA_UNMAP in a NEW Realm lies inside the
 * walk and becomes RIPAS_RAM (figure A5.4). Only an entry that is neither
 * VOID nor DATA, such as an ASSIGNED_DEV entry, stops the walk
 * (not_unassigned).
 *
 * The tests build a Realm in REALM_NEW with an RTT down to level 3,
 * install the entries directly the way rtt_data_unmap_tests.cpp does, and
 * run the handler over four pages.
 */

#define INIT_RIPAS_TEST_RTT_START_IDX		119000U
#define INIT_RIPAS_TEST_NS_LIST_START_IDX	127700U

#define INIT_RIPAS_TEST_PAGES	4UL
#define INIT_RIPAS_TEST_PAGE(n)	(TEST_DATA_IPA_BASE + ((n) * GRANULE_SIZE))
#define INIT_RIPAS_TEST_TOP	INIT_RIPAS_TEST_PAGE(INIT_RIPAS_TEST_PAGES)

TEST_GROUP(rtt_init_ripas_destroyed_tests) {
	TEST_SETUP()
	{
		static bool counters_initialized;

		if (!counters_initialized) {
			reset_data_granule_allocation();
			g_rtt_next_idx = INIT_RIPAS_TEST_RTT_START_IDX;
			g_ns_list_next_idx = INIT_RIPAS_TEST_NS_LIST_START_IDX;
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

/* Replace the level 3 entry of @ipa with an unassigned_destroyed entry. */
static void install_unassigned_destroyed(const struct test_data_ctx *ctx,
					 unsigned long ipa)
{
	struct s2tt_context s2_ctx;
	struct s2tt_walk wi;
	unsigned long *table;
	unsigned long s2tte;

	init_data_s2_ctx(ctx, &s2_ctx);
	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);
	s2tt_walk_lock_unlock(&s2_ctx, ipa, S2TT_PAGE_LEVEL, &wi);
	LONGS_EQUAL(S2TT_PAGE_LEVEL, wi.last_level);

	table = (unsigned long *)buffer_granule_mecid_map(wi.g_llt, SLOT_RTT,
							  s2_ctx.mecid);
	CHECK_TRUE(table != NULL);
	s2tte = s2tte_create_unassigned_destroyed(&s2_ctx,
						  s2tte_read(&table[wi.index]));
	s2tte_write(&table[wi.index], s2tte);
	buffer_unmap(table);
	granule_unlock(wi.g_llt);
}

static void expect_unassigned_ram(const struct test_data_ctx *ctx,
				  unsigned long ipa)
{
	struct s2tt_context s2_ctx;
	unsigned long s2tte;
	long level;

	init_data_s2_ctx(ctx, &s2_ctx);
	CHECK_TRUE(read_data_ipa_s2tte(ctx, ipa, &s2tte, &level));
	LONGS_EQUAL(S2TT_PAGE_LEVEL, level);
	CHECK_TRUE(s2tte_is_unassigned_ram(&s2_ctx, s2tte));
}

static void expect_assigned_ram(const struct test_data_ctx *ctx,
				unsigned long ipa, uintptr_t pa)
{
	struct s2tt_context s2_ctx;
	unsigned long s2tte;
	long level;

	init_data_s2_ctx(ctx, &s2_ctx);
	CHECK_TRUE(read_data_ipa_s2tte(ctx, ipa, &s2tte, &level));
	LONGS_EQUAL(S2TT_PAGE_LEVEL, level);
	CHECK_TRUE(s2tte_is_assigned_ram(&s2_ctx, s2tte, level));
	UNSIGNED_LONGS_EQUAL(pa, s2tte_pa(&s2_ctx, s2tte, level));
}

TEST(rtt_init_ripas_destroyed_tests, unassigned_destroyed_entry_becomes_ram)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	install_unassigned_destroyed(&ctx, INIT_RIPAS_TEST_PAGE(2));

	smc_rtt_init_ripas(ctx.rd, TEST_DATA_IPA_BASE, INIT_RIPAS_TEST_TOP,
			   &res);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(INIT_RIPAS_TEST_TOP, res.x[1]);
	for (unsigned long n = 0UL; n < INIT_RIPAS_TEST_PAGES; n++) {
		expect_unassigned_ram(&ctx, INIT_RIPAS_TEST_PAGE(n));
	}
}

TEST(rtt_init_ripas_destroyed_tests, assigned_destroyed_entry_becomes_ram)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	data_pa = reserve_delegated_granules(1U);
	CHECK_TRUE(install_assigned_destroyed_mapping(&ctx,
						      INIT_RIPAS_TEST_PAGE(1),
						      data_pa, S2TT_PAGE_LEVEL));

	smc_rtt_init_ripas(ctx.rd, TEST_DATA_IPA_BASE, INIT_RIPAS_TEST_TOP,
			   &res);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(INIT_RIPAS_TEST_TOP, res.x[1]);
	expect_unassigned_ram(&ctx, INIT_RIPAS_TEST_PAGE(0));
	expect_assigned_ram(&ctx, INIT_RIPAS_TEST_PAGE(1), data_pa);
	expect_unassigned_ram(&ctx, INIT_RIPAS_TEST_PAGE(2));
	expect_unassigned_ram(&ctx, INIT_RIPAS_TEST_PAGE(3));
}

/* An entry that is neither VOID nor DATA still ends the walk. */
TEST(rtt_init_ripas_destroyed_tests, device_entry_still_stops_the_walk)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t dev_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	dev_pa = reserve_delegated_granules(1U);
	CHECK_TRUE(install_assigned_dev_mapping(&ctx, INIT_RIPAS_TEST_PAGE(2),
						dev_pa, S2TT_PAGE_LEVEL));

	smc_rtt_init_ripas(ctx.rd, TEST_DATA_IPA_BASE, INIT_RIPAS_TEST_TOP,
			   &res);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(INIT_RIPAS_TEST_PAGE(2), res.x[1]);
	expect_unassigned_ram(&ctx, INIT_RIPAS_TEST_PAGE(0));
	expect_unassigned_ram(&ctx, INIT_RIPAS_TEST_PAGE(1));
}

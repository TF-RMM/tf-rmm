/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

#include "rtt_data_test_helpers.h"

/*
 * RMI_RTT_READ_ENTRY output address for device entries.
 *
 * DEN0137 2.0-bet3 B4.5.70.3 success conditions state_prot and state_io
 * require rtte.addr == walk.rtte.addr for an entry whose state is
 * RTTE_NARCH_DEV, whatever its RIPAS. Only RTTE_VOID and RTTE_UNMAPPED_NS
 * entries report a zero address (state_invalid).
 *
 * An assigned_dev entry with RIPAS_DESTROYED is reachable through
 * RMI_RTT_DEV_MAP, RMI_RTT_DEV_UNMAP (the RIPAS becomes DESTROYED) and a
 * second RMI_RTT_DEV_MAP of the same IPA, which preserves the RIPAS. The
 * device lifecycle is not available in host_test, so the entries are
 * installed directly in the same way rtt_data_unmap_tests.cpp installs
 * assigned_dev_dev entries.
 */

#define READ_ENTRY_TEST_RTT_START_IDX		95000U
#define READ_ENTRY_TEST_NS_LIST_START_IDX	126200U

/* A 4KB-aligned stand-in for a device PA; READ_ENTRY only decodes it. */
#define READ_ENTRY_TEST_DEV_PA		TEST_NS_PA

TEST_GROUP(rtt_read_entry_dev_tests) {
	TEST_SETUP()
	{
		static bool counters_initialized;

		if (!counters_initialized) {
			reset_data_granule_allocation();
			g_rtt_next_idx = READ_ENTRY_TEST_RTT_START_IDX;
			g_ns_list_next_idx = READ_ENTRY_TEST_NS_LIST_START_IDX;
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

/*
 * Install an assigned_dev_destroyed entry at level 3, mirroring
 * install_assigned_dev_mapping() but with RIPAS_DESTROYED.
 */
static bool install_assigned_dev_destroyed_mapping(
	const struct test_data_ctx *ctx, unsigned long ipa, uintptr_t dev_pa)
{
	struct s2tt_context s2_ctx;
	struct s2tt_walk wi;
	unsigned long *table;
	unsigned long dev_ap;
	unsigned long s2tte;

	init_data_s2_ctx(ctx, &s2_ctx);
	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);
	s2tt_walk_lock_unlock(&s2_ctx, ipa, S2TT_PAGE_LEVEL, &wi);
	if (wi.last_level != S2TT_PAGE_LEVEL) {
		granule_unlock(wi.g_llt);
		return false;
	}

	table = (unsigned long *)buffer_granule_mecid_map(wi.g_llt, SLOT_RTT,
							  s2_ctx.mecid);
	CHECK_TRUE(table != NULL);

	dev_ap = s2tte_update_prot_ap(&s2_ctx, 0UL,
				      S2TTE_DEV_DEF_BASE_PERM_IDX,
				      S2TTE_DEF_PROT_OVERLAY_IDX);
	s2tte = s2tte_create_assigned_dev_destroyed(&s2_ctx, dev_pa,
						    S2TT_PAGE_LEVEL, dev_ap);
	s2tte_write(&table[wi.index], s2tte);

	buffer_unmap(table);
	granule_unlock(wi.g_llt);
	return true;
}

static void read_entry_l3(const struct test_data_ctx *ctx,
			  struct smc_result *res)
{
	/* Seed the outputs so an untouched register is detected. */
	res->x[1] = 0xa5UL;
	res->x[2] = 0xa5UL;
	res->x[3] = 0xa5UL;
	res->x[4] = 0xa5UL;

	smc_rtt_read_entry(ctx->rd, TEST_DATA_IPA_BASE, S2TT_PAGE_LEVEL, res);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res->x[0]);
	UNSIGNED_LONGS_EQUAL((unsigned long)S2TT_PAGE_LEVEL, res->x[1]);
}

/* Control: an assigned_dev_dev entry reports its output address. */
TEST(rtt_read_entry_dev_tests, assigned_dev_dev_reports_address)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(install_assigned_dev_mapping(&ctx, TEST_DATA_IPA_BASE,
						READ_ENTRY_TEST_DEV_PA,
						S2TT_PAGE_LEVEL));

	read_entry_l3(&ctx, &res);

	UNSIGNED_LONGS_EQUAL(RMI_ASSIGNED_DEV, res.x[2]);
	UNSIGNED_LONGS_EQUAL(READ_ENTRY_TEST_DEV_PA, res.x[3]);
	UNSIGNED_LONGS_EQUAL((unsigned long)RIPAS_DEV, res.x[4]);
}

/* Control: an assigned_destroyed data entry reports its output address. */
TEST(rtt_read_entry_dev_tests, assigned_destroyed_reports_address)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	data_pa = reserve_delegated_granules(1U);
	CHECK_TRUE(install_assigned_destroyed_mapping(&ctx, TEST_DATA_IPA_BASE,
						      data_pa,
						      S2TT_PAGE_LEVEL));

	read_entry_l3(&ctx, &res);

	UNSIGNED_LONGS_EQUAL(RMI_ASSIGNED, res.x[2]);
	UNSIGNED_LONGS_EQUAL((unsigned long)data_pa, res.x[3]);
	UNSIGNED_LONGS_EQUAL((unsigned long)RIPAS_DESTROYED, res.x[4]);
}

/*
 * B4.5.70.3 state_prot / state_io: an assigned_dev entry whose RIPAS is
 * DESTROYED is still RTTE_NARCH_DEV and must report its output address,
 * like the two controls above.
 */
TEST(rtt_read_entry_dev_tests, assigned_dev_destroyed_reports_address)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(install_assigned_dev_destroyed_mapping(&ctx,
							  TEST_DATA_IPA_BASE,
							  READ_ENTRY_TEST_DEV_PA));

	read_entry_l3(&ctx, &res);

	UNSIGNED_LONGS_EQUAL(RMI_ASSIGNED_DEV, res.x[2]);
	UNSIGNED_LONGS_EQUAL(READ_ENTRY_TEST_DEV_PA, res.x[3]);
	UNSIGNED_LONGS_EQUAL((unsigned long)RIPAS_DESTROYED, res.x[4]);
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

#include "rtt_data_test_helpers.h"

/*
 * Common setup/teardown for all rtt_data_unmap_tests.
 *
 * TEST_SETUP initialises the host platform.  Granule allocation counters
 * are static and monotonically growing across tests in this group so each
 * test draws a fresh range of NS granules — this avoids the need to reset
 * the granule state-tracking table (which would corrupt RMM-internal
 * state owned by earlier boot/init).  The NS-list pool is moved to
 * DATA_TEST_NS_LIST_START_IDX once at startup to give room for up to 512
 * alignment-gap + data granules per test.
 */
TEST_GROUP(rtt_data_unmap_tests) {
	TEST_SETUP()
	{
		static bool counters_initialized;

		if (!counters_initialized) {
			reset_data_granule_allocation();
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
 * Helper: set up realm, create RTTs for [TEST_DATA_IPA_BASE, top), initialise
 * RIPAS=RAM, then delegate and map n contiguous data pages.
 * Returns the PA of the first data granule via data_base_out.
 */
static bool setup_and_map_pages(struct test_data_ctx *ctx,
				unsigned long ipa_base,
				unsigned long ipa_top,
				unsigned int n,
				uintptr_t *data_base_out)
{
	if (!create_data_rtt_ctx(ctx)) {
		return false;
	}
	if (!init_ripas_range(ctx, ipa_base, ipa_top)) {
		return false;
	}

	uintptr_t data_base = reserve_delegated_granules(n);

	if (!map_data_pages(ctx, ipa_base, data_base, n)) {
		return false;
	}

	*data_base_out = data_base;
	return true;
}

/* ------------------------------------------------------------------ */
/* Happy-path: L3 page, SINGLE output mode                            */
/* ------------------------------------------------------------------ */

/*
 * Maps one page at TEST_DATA_IPA_BASE, unmaps it with SINGLE mode.
 * Verifies:
 *  - ret0 == RMI_SUCCESS
 *  - ret1 == TEST_DATA_PAGE_TOP (out_top)
 *  - ret2 encodes the data PA, CNT=1
 *  - ret2 encodes SZ=L3 and ST=DELEGATED
 *  - ret3 == 0
 *  - data granule returns to DELEGATED state
 *  - RTT entry becomes unassigned_destroyed
 */
TEST(rtt_data_unmap_tests, l3_page_single_mode_happy_path)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;

	CHECK_TRUE(setup_and_map_pages(&ctx, TEST_DATA_IPA_BASE,
				       TEST_DATA_PAGE_TOP, 1U, &data_base));

	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE, TEST_DATA_PAGE_TOP,
			   make_unmap_flags_single(), 0UL, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_PAGE_TOP, res.x[1]);
	CHECK_EQUAL(data_base, decode_single_oaddr_pa(res.x[2]));
	CHECK_EQUAL(1UL, decode_rdesc_count(res.x[2]));
	CHECK_EQUAL(RMI_PAGE_L3, decode_rdesc_size(res.x[2]));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(res.x[2]));
	CHECK_EQUAL(0UL, res.x[3]);

	expect_data_granule_delegated(data_base);
	expect_ipa_unassigned_destroyed(&ctx, TEST_DATA_IPA_BASE);
}

/* ------------------------------------------------------------------ */
/* Happy-path: L3 page, NONE output mode                              */
/* ------------------------------------------------------------------ */

/*
 * Maps one page, unmaps it with NONE mode.
 * Verifies:
 *  - ret0 == RMI_SUCCESS
 *  - ret2 == 0 (no output descriptor)
 *  - ret3 == 0
 *  - data granule returns to DELEGATED state
 */
TEST(rtt_data_unmap_tests, l3_page_none_mode_happy_path)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;

	CHECK_TRUE(setup_and_map_pages(&ctx, TEST_DATA_IPA_BASE,
				       TEST_DATA_PAGE_TOP, 1U, &data_base));

	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE, TEST_DATA_PAGE_TOP,
			   make_unmap_flags_none(), 0UL, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(0UL, res.x[2]);
	CHECK_EQUAL(0UL, res.x[3]);

	expect_data_granule_delegated(data_base);
	expect_ipa_unassigned_destroyed(&ctx, TEST_DATA_IPA_BASE);
}

/* ------------------------------------------------------------------ */
/* Happy-path: two L3 pages, SINGLE mode (contiguous PAs)             */
/* ------------------------------------------------------------------ */

/*
 * Maps two contiguous pages, unmaps both with SINGLE in one call.
 * Since both pages map to contiguous PAs the descriptor covers count=2.
 */
TEST(rtt_data_unmap_tests, l3_two_pages_single_mode_contiguous)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;
	unsigned long top = TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE;

	CHECK_TRUE(setup_and_map_pages(&ctx, TEST_DATA_IPA_BASE, top,
				       2U, &data_base));

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags_single(), 0UL, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top, res.x[1]);
	CHECK_EQUAL(data_base, decode_single_oaddr_pa(res.x[2]));
	CHECK_EQUAL(2UL, decode_rdesc_count(res.x[2]));
	CHECK_EQUAL(RMI_PAGE_L3, decode_rdesc_size(res.x[2]));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(res.x[2]));

	expect_data_granules_delegated(data_base, 2U);
	expect_ipa_unassigned_destroyed(&ctx, TEST_DATA_IPA_BASE);
	expect_ipa_unassigned_destroyed(&ctx, TEST_DATA_IPA_BASE + GRANULE_SIZE);
}

/* ------------------------------------------------------------------ */
/* Happy-path: two L3 pages, LIST output mode                         */
/* ------------------------------------------------------------------ */

/*
 * Maps two contiguous pages, unmaps both with LIST mode.
 * The two contiguous PAs are merged by addr_list_add_block into a single
 * range descriptor, so ret3 == 1.
 */
TEST(rtt_data_unmap_tests, l3_two_pages_list_mode)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;
	uintptr_t list_pa = reserve_list_granule();
	unsigned long top = TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE;

	CHECK_TRUE(setup_and_map_pages(&ctx, TEST_DATA_IPA_BASE, top,
				       2U, &data_base));

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags(RMI_ADDR_TYPE_LIST, 2UL),
			   (unsigned long)list_pa, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top, res.x[1]);
	/* Two contiguous 4K pages merge into one range descriptor */
	CHECK_EQUAL(1UL, res.x[3]);

	/* Verify the output descriptor: base PA, count=2 */
	unsigned long rdesc = read_list_entry(list_pa, 0U);
	CHECK_EQUAL(data_base, decode_single_oaddr_pa(rdesc));
	CHECK_EQUAL(2UL, decode_rdesc_count(rdesc));
	CHECK_EQUAL(RMI_PAGE_L3, decode_rdesc_size(rdesc));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(rdesc));

	expect_data_granules_delegated(data_base, 2U);
	expect_ipa_unassigned_destroyed(&ctx, TEST_DATA_IPA_BASE);
	expect_ipa_unassigned_destroyed(&ctx, TEST_DATA_IPA_BASE + GRANULE_SIZE);
}

/* ------------------------------------------------------------------ */
/* Already-unmapped IPA returns SUCCESS with count=0                  */
/* ------------------------------------------------------------------ */

/*
 * Calls data_unmap on an IPA that has never been mapped.
 * Expects RMI_SUCCESS and no output descriptor (count=0).
 */
TEST(rtt_data_unmap_tests, already_unmapped_returns_success_no_output)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};

	CHECK_TRUE(create_data_rtt_ctx(&ctx));

	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE, TEST_DATA_PAGE_TOP,
			   make_unmap_flags_single(), 0UL, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_PAGE_TOP, res.x[1]);
	CHECK_EQUAL(0UL, res.x[2]);
}

/*
 * A partial range inside a non-live block is rejected at the block level, just
 * like a live block that is larger than the requested range.
 */
TEST(rtt_data_unmap_tests, partial_non_live_l2_block_fails)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	unsigned long top = TEST_DATA_IPA_BASE + (16UL * GRANULE_SIZE);
	return_code_t rc;

	CHECK_TRUE(create_data_rtt_ctx_l2_only(&ctx));

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags_none(), 0UL, &res);
	res = sro_complete_operation(res);

	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_ERROR_RTT, rc.status);
	CHECK_EQUAL(2U, rc.index);
	CHECK_EQUAL(0UL, res.x[1]);
}

/*
 * DATA unmap of assigned_empty and assigned_destroyed entries keeps the
 * matching RIPAS state in the resulting unassigned entry and needs no TLBI.
 */
TEST(rtt_data_unmap_tests, assigned_empty_and_destroyed_entries)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;
	unsigned long empty_ipa = TEST_DATA_IPA_BASE;
	unsigned long destroyed_ipa = TEST_DATA_IPA_BASE + GRANULE_SIZE;
	unsigned long top = TEST_DATA_IPA_BASE + (2UL * GRANULE_SIZE);

	CHECK_TRUE(setup_and_map_pages(&ctx, TEST_DATA_IPA_BASE, top,
				       2U, &data_base));
	CHECK_TRUE(install_assigned_empty_mapping(&ctx, empty_ipa,
						  data_base,
						  S2TT_PAGE_LEVEL));
	CHECK_TRUE(install_assigned_destroyed_mapping(&ctx, destroyed_ipa,
						      data_base +
						      GRANULE_SIZE,
						      S2TT_PAGE_LEVEL));

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags_none(), 0UL, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top, res.x[1]);
	CHECK_EQUAL(0UL, res.x[2]);
	CHECK_EQUAL(0UL, res.x[3]);

	expect_data_granules_delegated(data_base, 2U);
	expect_ipa_unassigned_empty(&ctx, empty_ipa);
	expect_ipa_unassigned_destroyed(&ctx, destroyed_ipa);
}

/* ------------------------------------------------------------------ */
/* L2 block via fold: SINGLE output mode                              */
/* ------------------------------------------------------------------ */

/*
 * Maps a full L3 table (512 pages at 2MB-aligned PAs), folds to an L2 block,
 * then unmaps the block with SINGLE mode.
 * Verifies:
 *  - ret0 == RMI_SUCCESS
 *  - ret1 == TEST_DATA_L2_BLOCK_TOP (out_top)
 *  - ret2 encodes the block PA, CNT=1
 *  - ret2 encodes SZ=L2 and ST=DELEGATED
 *  - all 512 data granules are DELEGATED
 */
TEST(rtt_data_unmap_tests, l2_block_single_mode_via_fold)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;

	if (!create_data_rtt_ctx(&ctx)) {
		CHECK_TRUE(false);
		return;
	}
	if (!init_ripas_range(&ctx, TEST_DATA_IPA_BASE, TEST_DATA_L2_BLOCK_TOP)) {
		CHECK_TRUE(false);
		return;
	}

	/*
	 * Allocate 512 contiguous data granules at a 2MB-aligned PA so that
	 * smc_rtt_fold can verify the contiguous block requirement.
	 */
	data_base = reserve_delegated_granules_l2_aligned((unsigned int)S2TTES_PER_S2TT);

	CHECK_TRUE(map_data_pages(&ctx, TEST_DATA_IPA_BASE, data_base,
				  (unsigned int)S2TTES_PER_S2TT));
	CHECK_TRUE(fold_to_l2(&ctx, TEST_DATA_IPA_BASE));

	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE, TEST_DATA_L2_BLOCK_TOP,
			   make_unmap_flags_single(), 0UL, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_L2_BLOCK_TOP, res.x[1]);
	CHECK_EQUAL(data_base, decode_single_oaddr_pa(res.x[2]));
	CHECK_EQUAL(1UL, decode_rdesc_count(res.x[2]));
	CHECK_EQUAL(RMI_BLOCK_L2, decode_rdesc_size(res.x[2]));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(res.x[2]));
	CHECK_EQUAL(0UL, res.x[3]);

	expect_data_granules_delegated(data_base, (unsigned int)S2TTES_PER_S2TT);
}

/* ------------------------------------------------------------------ */
/* L2 block via fold: NONE output mode                                */
/* ------------------------------------------------------------------ */

/*
 * Maps a full L3 table, folds it into one L2 block, then unmaps the block
 * with NONE output mode. Verifies that no descriptor is returned and all
 * backing data granules return to DELEGATED.
 */
TEST(rtt_data_unmap_tests, l2_block_none_mode_via_fold)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;

	if (!create_data_rtt_ctx(&ctx)) {
		CHECK_TRUE(false);
		return;
	}
	if (!init_ripas_range(&ctx, TEST_DATA_IPA_BASE, TEST_DATA_L2_BLOCK_TOP)) {
		CHECK_TRUE(false);
		return;
	}
	data_base = reserve_delegated_granules_l2_aligned((unsigned int)S2TTES_PER_S2TT);
	CHECK_TRUE(map_data_pages(&ctx, TEST_DATA_IPA_BASE, data_base,
				  (unsigned int)S2TTES_PER_S2TT));
	CHECK_TRUE(fold_to_l2(&ctx, TEST_DATA_IPA_BASE));

	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE, TEST_DATA_L2_BLOCK_TOP,
			   make_unmap_flags_none(), 0UL, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(0UL, res.x[2]);
	CHECK_EQUAL(0UL, res.x[3]);

	expect_data_granules_delegated(data_base, (unsigned int)S2TTES_PER_S2TT);
}

/* ------------------------------------------------------------------ */
/* L2 block via fold: LIST output mode                                */
/* ------------------------------------------------------------------ */

/*
 * The L2 block is a single 2MB entry.  addr_list_add_block encodes it as
 * one range descriptor, so ret3 == 1 with CNT=1.
 */
TEST(rtt_data_unmap_tests, l2_block_list_mode_via_fold)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;
	uintptr_t list_pa = reserve_list_granule();

	if (!create_data_rtt_ctx(&ctx)) {
		CHECK_TRUE(false);
		return;
	}
	if (!init_ripas_range(&ctx, TEST_DATA_IPA_BASE, TEST_DATA_L2_BLOCK_TOP)) {
		CHECK_TRUE(false);
		return;
	}
	data_base = reserve_delegated_granules_l2_aligned((unsigned int)S2TTES_PER_S2TT);
	CHECK_TRUE(map_data_pages(&ctx, TEST_DATA_IPA_BASE, data_base,
				  (unsigned int)S2TTES_PER_S2TT));
	CHECK_TRUE(fold_to_l2(&ctx, TEST_DATA_IPA_BASE));

	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE, TEST_DATA_L2_BLOCK_TOP,
			   make_unmap_flags(RMI_ADDR_TYPE_LIST, 1UL),
			   (unsigned long)list_pa, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(1UL, res.x[3]);

	unsigned long rdesc = read_list_entry(list_pa, 0U);
	CHECK_EQUAL(data_base, decode_single_oaddr_pa(rdesc));
	CHECK_EQUAL(1UL, decode_rdesc_count(rdesc));
	CHECK_EQUAL(RMI_BLOCK_L2, decode_rdesc_size(rdesc));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(rdesc));

	expect_data_granules_delegated(data_base, (unsigned int)S2TTES_PER_S2TT);
}

/*
 * Unmaps one full L2 block, then stops successfully at the next live L2 block
 * because the requested top only covers a partial block. This exercises the
 * non-first block-overflow path in rtt_unmap_one_table().
 */
TEST(rtt_data_unmap_tests, l2_block_stops_before_partial_next_block)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;
	uintptr_t second_base = 0UL;
	uintptr_t rtt_l3_second;
	unsigned long second_ipa = TEST_DATA_L2_BLOCK_TOP;
	unsigned long second_top = second_ipa + TEST_DATA_L2_BLOCK_SIZE;
	unsigned long partial_top = second_ipa + GRANULE_SIZE;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	rtt_l3_second = reserve_delegated_granules(1U);
	CHECK_EQUAL(RMI_SUCCESS,
		    smc_rtt_create(ctx.rd, rtt_l3_second, second_ipa, 3UL));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, second_top));

	data_base = reserve_delegated_granules_l2_aligned(
				(unsigned int)S2TTES_PER_S2TT);
	CHECK_TRUE(map_data_pages(&ctx, TEST_DATA_IPA_BASE, data_base,
				  (unsigned int)S2TTES_PER_S2TT));
	CHECK_TRUE(fold_to_l2(&ctx, TEST_DATA_IPA_BASE));

	second_base = reserve_delegated_granules_l2_aligned(
				(unsigned int)S2TTES_PER_S2TT);
	CHECK_TRUE(map_data_pages(&ctx, second_ipa, second_base,
				  (unsigned int)S2TTES_PER_S2TT));
	CHECK_TRUE(fold_to_l2(&ctx, second_ipa));

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, partial_top,
			   make_unmap_flags_single(), 0UL, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(second_ipa, res.x[1]);
	CHECK_EQUAL(data_base, decode_single_oaddr_pa(res.x[2]));
	CHECK_EQUAL(1UL, decode_rdesc_count(res.x[2]));
	CHECK_EQUAL(RMI_BLOCK_L2, decode_rdesc_size(res.x[2]));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(res.x[2]));
	CHECK_EQUAL(0UL, res.x[3]);

	expect_data_granules_delegated(data_base, (unsigned int)S2TTES_PER_S2TT);
	expect_ipa_unassigned_destroyed(&ctx, TEST_DATA_IPA_BASE);
	expect_data_granules_data_state(second_base,
					(unsigned int)S2TTES_PER_S2TT);
	expect_ipa_assigned_ram_to_pa(&ctx, second_ipa, second_base, 2L);

	smc_rtt_data_unmap(ctx.rd, second_ipa, second_top,
			   make_unmap_flags_single(), 0UL, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(second_top, res.x[1]);
	CHECK_EQUAL(second_base, decode_single_oaddr_pa(res.x[2]));
	CHECK_EQUAL(1UL, decode_rdesc_count(res.x[2]));
	CHECK_EQUAL(RMI_BLOCK_L2, decode_rdesc_size(res.x[2]));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(res.x[2]));
	CHECK_EQUAL(0UL, res.x[3]);

	expect_data_granules_delegated(second_base,
				       (unsigned int)S2TTES_PER_S2TT);
	expect_ipa_unassigned_destroyed(&ctx, second_ipa);
}

/* ------------------------------------------------------------------ */
/* Error cases                                                         */
/* ------------------------------------------------------------------ */

/* rd_align: rd address not granule-aligned */
TEST(rtt_data_unmap_tests, rd_unaligned)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	smc_rtt_data_unmap(ctx.rd + 1UL,
			   TEST_DATA_IPA_BASE, TEST_DATA_PAGE_TOP,
			   make_unmap_flags_none(), 0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* rd_state: passing an RTT granule where rd is expected */
TEST(rtt_data_unmap_tests, rd_wrong_state)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	smc_rtt_data_unmap(ctx.rtt_l0,
			   TEST_DATA_IPA_BASE, TEST_DATA_PAGE_TOP,
			   make_unmap_flags_none(), 0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ipa_bound: base is outside the PAR (unprotected IPA space) */
TEST(rtt_data_unmap_tests, base_outside_par)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	/* TEST_PAR_SIZE is the start of the unprotected range */
	unsigned long unprotected_base = TEST_PAR_SIZE;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	smc_rtt_data_unmap(ctx.rd,
			   unprotected_base,
			   unprotected_base + GRANULE_SIZE,
			   make_unmap_flags_none(), 0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ipa_bound: top crosses into the unprotected IPA space */
TEST(rtt_data_unmap_tests, top_outside_par)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	unsigned long base = TEST_PAR_SIZE - GRANULE_SIZE;
	unsigned long top = TEST_PAR_SIZE + GRANULE_SIZE;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	smc_rtt_data_unmap(ctx.rd,
			   base, top,
			   make_unmap_flags_none(), 0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ipa_bound: base is outside the realm IPA size */
TEST(rtt_data_unmap_tests, base_outside_realm_ipa_size)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	unsigned long ipa_size = 1UL << TEST_IPA_BITS;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	smc_rtt_data_unmap(ctx.rd,
			   ipa_size,
			   ipa_size + GRANULE_SIZE,
			   make_unmap_flags_none(), 0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* base_align: base is not granule-aligned */
TEST(rtt_data_unmap_tests, base_unaligned)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE + 1UL,
			   TEST_DATA_IPA_BASE + 1UL + GRANULE_SIZE,
			   make_unmap_flags_none(), 0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* top_align: top is not granule-aligned */
TEST(rtt_data_unmap_tests, top_unaligned)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE,
			   TEST_DATA_PAGE_TOP + 1UL,
			   make_unmap_flags_none(), 0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* size_valid: top <= base */
TEST(rtt_data_unmap_tests, top_equal_base)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE,
			   TEST_DATA_IPA_BASE,
			   make_unmap_flags_none(), 0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* oaddr_type: reserved oaddr_type value */
TEST(rtt_data_unmap_tests, invalid_oaddr_type)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	/* oaddr_type field = 3 is reserved */
	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE, TEST_DATA_PAGE_TOP,
			   INPLACE(RMI_RTT_UNMAP_FLAGS_OADDR_TYPE, 3UL),
			   0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* oaddr_sbz: oaddr non-zero when oaddr_type != LIST */
TEST(rtt_data_unmap_tests, oaddr_sbz_violation_single_mode)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t dummy = reserve_list_granule();

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE, TEST_DATA_PAGE_TOP,
			   make_unmap_flags_single(),
			   (unsigned long)dummy, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* list_count: LIST mode requires a non-zero descriptor count */
TEST(rtt_data_unmap_tests, list_count_zero_is_invalid)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t list_pa = reserve_list_granule();

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE, TEST_DATA_PAGE_TOP,
			   make_unmap_flags(RMI_ADDR_TYPE_LIST, 0UL),
			   (unsigned long)list_pa, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* oaddr_align: LIST output address must be unsigned-long-aligned */
TEST(rtt_data_unmap_tests, list_oaddr_must_be_aligned)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t list_pa = reserve_list_granule();

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE, TEST_DATA_PAGE_TOP,
			   make_unmap_flags(RMI_ADDR_TYPE_LIST, 1UL),
			   (unsigned long)list_pa + 1UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* rtte_align: block mapped at L2 but unmap called with page-granular range */
TEST(rtt_data_unmap_tests, rtte_align_mismatch_l2_block)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;

	if (!create_data_rtt_ctx(&ctx)) {
		CHECK_TRUE(false);
		return;
	}
	if (!init_ripas_range(&ctx, TEST_DATA_IPA_BASE, TEST_DATA_L2_BLOCK_TOP)) {
		CHECK_TRUE(false);
		return;
	}
	data_base = reserve_delegated_granules_l2_aligned((unsigned int)S2TTES_PER_S2TT);
	CHECK_TRUE(map_data_pages(&ctx, TEST_DATA_IPA_BASE, data_base,
				  (unsigned int)S2TTES_PER_S2TT));
	CHECK_TRUE(fold_to_l2(&ctx, TEST_DATA_IPA_BASE));

	/*
	 * [0, 4KB) is not L2-aligned (base is aligned but range is too small
	 * for an L2 block entry).
	 */
	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE,
			   TEST_DATA_IPA_BASE + GRANULE_SIZE,
			   make_unmap_flags_single(), 0UL, &res);

	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_ERROR_RTT, rc.status);
	CHECK_EQUAL(0UL, res.x[1]);
}

/*
 * rtte_align_base_not_l2_aligned: L2 block mapped at TEST_DATA_IPA_BASE.
 * Call unmap with base = L2_BASE + GRANULE_SIZE (not L2-aligned) but range
 * >= 2MB so the range-size check passes.  The !validate_map_addr branch
 * fires → RMI_ERROR_RTT at level 2.
 * Covers the !validate_map_addr sub-expression in the rtte_align condition
 * (rtt.c line ~2060, OR branch not hit by rtte_align_mismatch_l2_block).
 */
TEST(rtt_data_unmap_tests, rtte_align_base_not_l2_aligned)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;

	if (!create_data_rtt_ctx(&ctx)) {
		CHECK_TRUE(false);
		return;
	}
	if (!init_ripas_range(&ctx, TEST_DATA_IPA_BASE, TEST_DATA_L2_BLOCK_TOP)) {
		CHECK_TRUE(false);
		return;
	}
	data_base = reserve_delegated_granules_l2_aligned((unsigned int)S2TTES_PER_S2TT);
	CHECK_TRUE(map_data_pages(&ctx, TEST_DATA_IPA_BASE, data_base,
				  (unsigned int)S2TTES_PER_S2TT));
	CHECK_TRUE(fold_to_l2(&ctx, TEST_DATA_IPA_BASE));

	/*
	 * base is granule-aligned but NOT L2-aligned; range is >= 2MB so the
	 * (top-base) < map_size check does NOT fire.  Only !validate_map_addr
	 * fires, triggering RMI_ERROR_RTT at level 2.
	 */
	unsigned long misaligned_base = TEST_DATA_IPA_BASE + GRANULE_SIZE;
	unsigned long misaligned_top  = misaligned_base + TEST_DATA_L2_BLOCK_SIZE;

	smc_rtt_data_unmap(ctx.rd,
			   misaligned_base, misaligned_top,
			   make_unmap_flags_single(), 0UL, &res);

	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_ERROR_RTT, rc.status);
	CHECK_EQUAL(2U, rc.index);
	CHECK_EQUAL(0UL, res.x[1]);
}

/*
 * Non-live entries are skipped before output descriptors are emitted, so all
 * output modes can advance across holes. SINGLE also requires the returned live
 * PAs to stay contiguous. This test checks the NONE mode case, including
 * progress to the requested top.
 *
 * Map pages at IPA+0 and IPA+2*GRANULE_SIZE, leaving IPA+1 unmapped.
 */
TEST(rtt_data_unmap_tests, none_mode_skips_non_live_entries)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	unsigned long top3 = TEST_DATA_IPA_BASE + 3UL * GRANULE_SIZE;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, top3));

	/* Map pages at index 0 and 2; leave index 1 unassigned (non-live) */
	uintptr_t pa0 = reserve_delegated_granules(1U);
	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE, pa0));

	uintptr_t pa2 = reserve_delegated_granules(1U);
	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE, pa2));

	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE, top3,
			   make_unmap_flags_none(), 0UL, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top3, res.x[1]);
	/* Both mapped pages should be returned to DELEGATED */
	expect_data_granule_delegated(pa0);
	expect_data_granule_delegated(pa2);
}

/*
 * SINGLE output mode constrains the output PA range, not IPA continuity.
 * A non-live IPA hole between two live entries is skipped as long as the
 * returned PAs remain contiguous.
 */
TEST(rtt_data_unmap_tests, single_mode_skips_non_live_entries)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	unsigned long top3 = TEST_DATA_IPA_BASE + 3UL * GRANULE_SIZE;
	uintptr_t data_base;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, top3));

	data_base = reserve_delegated_granules(2U);
	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE, data_base));
	CHECK_TRUE(map_data_page(&ctx,
				 TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE,
				 data_base + GRANULE_SIZE));

	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE, top3,
			   make_unmap_flags_single(), 0UL, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top3, res.x[1]);
	CHECK_EQUAL(data_base, decode_single_oaddr_pa(res.x[2]));
	CHECK_EQUAL(2UL, decode_rdesc_count(res.x[2]));
	CHECK_EQUAL(RMI_PAGE_L3, decode_rdesc_size(res.x[2]));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(res.x[2]));
	expect_data_granules_delegated(data_base, 2U);
}

/*
 * Maps four live pages to contiguous PAs while leaving IPA holes between
 * them. SINGLE mode should skip the holes and return one contiguous PA
 * descriptor covering all live pages.
 */
TEST(rtt_data_unmap_tests, single_mode_skips_multiple_holes_with_contiguous_pa)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base;
	unsigned long top = TEST_DATA_IPA_BASE + 7UL * GRANULE_SIZE;
	static const unsigned int live_idx[] = {0U, 2U, 4U, 6U};
	const unsigned int live_count = sizeof(live_idx) / sizeof(live_idx[0]);

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, top));

	data_base = reserve_delegated_granules(live_count);
	for (unsigned int i = 0U; i < live_count; i++) {
		unsigned long ipa = TEST_DATA_IPA_BASE +
				    (unsigned long)live_idx[i] * GRANULE_SIZE;
		uintptr_t data_pa = data_base + (uintptr_t)i * GRANULE_SIZE;

		CHECK_TRUE(map_data_page(&ctx, ipa, data_pa));
	}

	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE, top,
			   make_unmap_flags_single(), 0UL, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top, res.x[1]);
	CHECK_EQUAL(data_base, decode_single_oaddr_pa(res.x[2]));
	CHECK_EQUAL(live_count, decode_rdesc_count(res.x[2]));
	CHECK_EQUAL(RMI_PAGE_L3, decode_rdesc_size(res.x[2]));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(res.x[2]));

	expect_data_granules_delegated(data_base, live_count);
	for (unsigned int i = 0U; i < live_count; i++) {
		unsigned long ipa = TEST_DATA_IPA_BASE +
				    (unsigned long)live_idx[i] * GRANULE_SIZE;

		expect_ipa_unassigned_destroyed(&ctx, ipa);
	}
}

/*
 * Maps live pages after a leading non-live IPA and leaves further holes
 * between and after them. DATA_UNMAP should skip every non-live entry in the
 * range, including the first one, and still return one SINGLE descriptor
 * because the live PAs are contiguous.
 */
TEST(rtt_data_unmap_tests, single_mode_skips_leading_and_all_non_live_entries)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base;
	unsigned long top = TEST_DATA_IPA_BASE + 7UL * GRANULE_SIZE;
	static const unsigned int live_idx[] = {1U, 3U, 5U};
	static const unsigned int hole_idx[] = {0U, 2U, 4U, 6U};
	const unsigned int live_count = sizeof(live_idx) / sizeof(live_idx[0]);
	const unsigned int hole_count = sizeof(hole_idx) / sizeof(hole_idx[0]);

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, top));

	data_base = reserve_delegated_granules(live_count);
	for (unsigned int i = 0U; i < live_count; i++) {
		unsigned long ipa = TEST_DATA_IPA_BASE +
				    (unsigned long)live_idx[i] * GRANULE_SIZE;
		uintptr_t data_pa = data_base + (uintptr_t)i * GRANULE_SIZE;

		CHECK_TRUE(map_data_page(&ctx, ipa, data_pa));
	}

	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE, top,
			   make_unmap_flags_single(), 0UL, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top, res.x[1]);
	CHECK_EQUAL(data_base, decode_single_oaddr_pa(res.x[2]));
	CHECK_EQUAL(live_count, decode_rdesc_count(res.x[2]));
	CHECK_EQUAL(RMI_PAGE_L3, decode_rdesc_size(res.x[2]));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(res.x[2]));

	expect_data_granules_delegated(data_base, live_count);
	for (unsigned int i = 0U; i < live_count; i++) {
		unsigned long ipa = TEST_DATA_IPA_BASE +
				    (unsigned long)live_idx[i] * GRANULE_SIZE;

		expect_ipa_unassigned_destroyed(&ctx, ipa);
	}
	for (unsigned int i = 0U; i < hole_count; i++) {
		unsigned long ipa = TEST_DATA_IPA_BASE +
				    (unsigned long)hole_idx[i] * GRANULE_SIZE;

		expect_ipa_unassigned_no_drain(&ctx, ipa);
	}
}

/*
 * SINGLE output mode stops before a live entry whose PA is not contiguous with
 * the descriptor already being returned.
 *
 * Map two contiguous IPAs to non-contiguous PAs. The first page is unmapped,
 * out_top points to the second IPA, and the second mapping remains live.
 */
TEST(rtt_data_unmap_tests, single_mode_stops_at_pa_discontinuity)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	unsigned long top2 = TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, top2));

	/*
	 * Reserve two separate, non-contiguous delegated granules.
	 * Reserve an unused granule between them to create the PA gap.
	 */
	uintptr_t pa0 = reserve_delegated_granules(1U);
	uintptr_t gap_pa = reserve_delegated_granules(1U);
	uintptr_t pa1 = reserve_delegated_granules(1U);
	CHECK_EQUAL(pa0 + GRANULE_SIZE, gap_pa);
	CHECK_EQUAL(gap_pa + GRANULE_SIZE, pa1);

	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE, pa0));
	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE + GRANULE_SIZE, pa1));

	/* SINGLE mode: should unmap only pa0, then stop at discontinuity */
	smc_rtt_data_unmap(ctx.rd,
			   TEST_DATA_IPA_BASE, top2,
			   make_unmap_flags_single(), 0UL, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	/* out_top = base + 1*GRANULE_SIZE (only first entry unmapped) */
	CHECK_EQUAL(TEST_DATA_IPA_BASE + GRANULE_SIZE, res.x[1]);
	/* ret2 should encode pa0 with CNT=1 and SZ=L3. */
	CHECK_EQUAL(pa0, decode_single_oaddr_pa(res.x[2]));
	CHECK_EQUAL(1UL, decode_rdesc_count(res.x[2]));
	CHECK_EQUAL(RMI_PAGE_L3, decode_rdesc_size(res.x[2]));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(res.x[2]));
	expect_data_granule_delegated(pa0);
	/* pa1 should still be DATA (second page not unmapped) */
	expect_data_granule_data_state(pa1);
}

/*
 * Maps live pages at sparse IPAs. LIST mode should skip non-live holes,
 * merge the first two PA-contiguous data pages into one descriptor, and
 * create a second descriptor for the later PA-discontiguous page.
 */
TEST(rtt_data_unmap_tests, list_mode_skips_holes_and_splits_pa_ranges)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t list_pa = reserve_list_granule();
	uintptr_t data_base;
	uintptr_t second_base;
	unsigned long top = TEST_DATA_IPA_BASE + 5UL * GRANULE_SIZE;
	unsigned long rdesc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, top));

	data_base = reserve_delegated_granules(2U);
	g_rtt_next_idx++;
	second_base = reserve_delegated_granules(1U);

	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE, data_base));
	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE,
				 data_base + GRANULE_SIZE));
	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE + 4UL * GRANULE_SIZE,
				 second_base));

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags(RMI_ADDR_TYPE_LIST, 4UL),
			   (unsigned long)list_pa, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top, res.x[1]);
	CHECK_EQUAL(2UL, res.x[3]);

	rdesc = read_list_entry(list_pa, 0U);
	CHECK_EQUAL(data_base, decode_single_oaddr_pa(rdesc));
	CHECK_EQUAL(2UL, decode_rdesc_count(rdesc));
	CHECK_EQUAL(RMI_PAGE_L3, decode_rdesc_size(rdesc));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(rdesc));

	rdesc = read_list_entry(list_pa, 1U);
	CHECK_EQUAL(second_base, decode_single_oaddr_pa(rdesc));
	CHECK_EQUAL(1UL, decode_rdesc_count(rdesc));
	CHECK_EQUAL(RMI_PAGE_L3, decode_rdesc_size(rdesc));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(rdesc));

	expect_data_granules_delegated(data_base, 2U);
	expect_data_granule_delegated(second_base);
	expect_ipa_unassigned_destroyed(&ctx, TEST_DATA_IPA_BASE);
	expect_ipa_unassigned_destroyed(&ctx, TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE);
	expect_ipa_unassigned_destroyed(&ctx, TEST_DATA_IPA_BASE + 4UL * GRANULE_SIZE);
}

/*
 * Maps two data pages separated by an IPA hole and limits LIST output to one
 * entry. The first page is unmapped, the hole is skipped, and processing
 * stops before the second live page because a new descriptor cannot fit.
 */
TEST(rtt_data_unmap_tests, list_mode_count_limit_stops_after_skipping_hole)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t list_pa = reserve_list_granule();
	uintptr_t first_pa;
	uintptr_t second_pa;
	unsigned long top = TEST_DATA_IPA_BASE + 3UL * GRANULE_SIZE;
	unsigned long rdesc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, top));

	first_pa = reserve_delegated_granules(1U);
	g_rtt_next_idx++;
	second_pa = reserve_delegated_granules(1U);

	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE, first_pa));
	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE,
				 second_pa));

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags(RMI_ADDR_TYPE_LIST, 1UL),
			   (unsigned long)list_pa, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE, res.x[1]);
	CHECK_EQUAL(1UL, res.x[3]);

	rdesc = read_list_entry(list_pa, 0U);
	CHECK_EQUAL(first_pa, decode_single_oaddr_pa(rdesc));
	CHECK_EQUAL(1UL, decode_rdesc_count(rdesc));
	CHECK_EQUAL(RMI_PAGE_L3, decode_rdesc_size(rdesc));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(rdesc));

	expect_data_granule_delegated(first_pa);
	expect_data_granule_data_state(second_pa);
	expect_ipa_unassigned_destroyed(&ctx, TEST_DATA_IPA_BASE);
	expect_ipa_assigned_ram(&ctx, TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE);
}

/*
 * Maps two data pages separated by an IPA hole and supplies an oversized
 * LIST_COUNT with the output pointer at the final descriptor slot in the NS
 * granule. The validator clips the effective output list to one entry.
 */
TEST(rtt_data_unmap_tests, list_mode_oversized_count_clipped_to_granule)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t list_pa = reserve_list_granule();
	uintptr_t oaddr = list_pa +
			  (((uintptr_t)ADDR_LIST_MAX_RANGES - 1UL) *
			   sizeof(unsigned long));
	uintptr_t first_pa;
	uintptr_t second_pa;
	unsigned long top = TEST_DATA_IPA_BASE + 3UL * GRANULE_SIZE;
	unsigned long rdesc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, top));

	first_pa = reserve_delegated_granules(1U);
	g_rtt_next_idx++;
	second_pa = reserve_delegated_granules(1U);

	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE, first_pa));
	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE,
				 second_pa));

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags(RMI_ADDR_TYPE_LIST,
					    (unsigned long)ADDR_LIST_MAX_RANGES +
					    100UL),
			   (unsigned long)oaddr, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE, res.x[1]);
	CHECK_EQUAL(1UL, res.x[3]);

	rdesc = read_list_entry(list_pa,
				(unsigned int)ADDR_LIST_MAX_RANGES - 1U);
	CHECK_EQUAL(first_pa, decode_single_oaddr_pa(rdesc));
	CHECK_EQUAL(1UL, decode_rdesc_count(rdesc));
	CHECK_EQUAL(RMI_PAGE_L3, decode_rdesc_size(rdesc));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(rdesc));

	expect_data_granule_delegated(first_pa);
	expect_data_granule_data_state(second_pa);
	expect_ipa_unassigned_destroyed(&ctx, TEST_DATA_IPA_BASE);
	expect_ipa_assigned_ram(&ctx, TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE);
}

/*
 * Places a device mapping at the first IPA and a data page after it.
 * DATA_UNMAP must reject the range with RMI_ERROR_RTT and leave both
 * mappings unchanged.
 */
TEST(rtt_data_unmap_tests, device_page_first_returns_rtt_error)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;
	unsigned long top = TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE;
	return_code_t rc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, top));

	CHECK_TRUE(install_assigned_dev_mapping(&ctx, TEST_DATA_IPA_BASE,
						TEST_NS_PA, S2TT_PAGE_LEVEL));
	data_pa = reserve_delegated_granules(1U);
	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE + GRANULE_SIZE,
				 data_pa));

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags_single(), 0UL, &res);

	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_ERROR_RTT, rc.status);
	CHECK_EQUAL(S2TT_PAGE_LEVEL, rc.index);
	CHECK_EQUAL(0UL, res.x[1]);

	expect_ipa_assigned_dev_dev(&ctx, TEST_DATA_IPA_BASE, S2TT_PAGE_LEVEL);
	expect_data_granule_data_state(data_pa);
	expect_ipa_assigned_ram(&ctx, TEST_DATA_IPA_BASE + GRANULE_SIZE);
}

/*
 * Places a device mapping after an initial data page. DATA_UNMAP should
 * return successful partial progress for the data page and stop before
 * touching the device mapping or the later data page.
 */
TEST(rtt_data_unmap_tests, data_unmap_stops_before_device_page_after_data)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t list_pa = reserve_list_granule();
	uintptr_t first_pa;
	uintptr_t second_pa;
	unsigned long top = TEST_DATA_IPA_BASE + 3UL * GRANULE_SIZE;
	unsigned long rdesc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, top));

	first_pa = reserve_delegated_granules(1U);
	second_pa = reserve_delegated_granules(1U);
	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE, first_pa));
	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE,
				 second_pa));
	CHECK_TRUE(install_assigned_dev_mapping(&ctx,
						TEST_DATA_IPA_BASE + GRANULE_SIZE,
						TEST_NS_PA_ALT,
						S2TT_PAGE_LEVEL));

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags(RMI_ADDR_TYPE_LIST, 2UL),
			   (unsigned long)list_pa, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_IPA_BASE + GRANULE_SIZE, res.x[1]);
	CHECK_EQUAL(1UL, res.x[3]);

	rdesc = read_list_entry(list_pa, 0U);
	CHECK_EQUAL(first_pa, decode_single_oaddr_pa(rdesc));
	CHECK_EQUAL(1UL, decode_rdesc_count(rdesc));
	CHECK_EQUAL(RMI_PAGE_L3, decode_rdesc_size(rdesc));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(rdesc));

	expect_data_granule_delegated(first_pa);
	expect_ipa_unassigned_destroyed(&ctx, TEST_DATA_IPA_BASE);
	expect_ipa_assigned_dev_dev(&ctx, TEST_DATA_IPA_BASE + GRANULE_SIZE,
				    S2TT_PAGE_LEVEL);
	expect_data_granule_data_state(second_pa);
	expect_ipa_assigned_ram(&ctx, TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE);
}

/*
 * Maps sparse data pages across three L3 tables using deliberately gapped
 * PAs. DATA_UNMAP processes at most one leaf RTT per call, so the host
 * must reissue with the previous result's @res.x[1] as the new base
 * until the requested range is fully covered. LIST mode in each call
 * should skip holes within the current leaf and emit descriptors in
 * IPA order without merging PA-discontiguous entries.
 */
TEST(rtt_data_unmap_tests, list_mode_random_pa_spans_multiple_l3_tables)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t list_pa = reserve_list_granule();
	uintptr_t data_pa[4U];
	unsigned long rdesc;
	unsigned long second_l3 = TEST_DATA_L2_BLOCK_TOP;
	unsigned long third_l3 = TEST_DATA_L2_BLOCK_TOP + TEST_DATA_L2_BLOCK_SIZE;
	unsigned long ipa[4U] = {
		TEST_DATA_L2_BLOCK_TOP - GRANULE_SIZE,
		second_l3,
		second_l3 + 7UL * GRANULE_SIZE,
		third_l3 + 3UL * GRANULE_SIZE,
	};
	unsigned long top = ipa[3] + GRANULE_SIZE;
	unsigned int next_ipa_idx = 0U;
	unsigned long cur_base;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(create_data_l3_rtt(&ctx, second_l3));
	CHECK_TRUE(create_data_l3_rtt(&ctx, third_l3));

	data_pa[0] = reserve_delegated_granules(1U);
	g_rtt_next_idx += 5U;
	data_pa[1] = reserve_delegated_granules(1U);
	g_rtt_next_idx += 2U;
	data_pa[2] = reserve_delegated_granules(1U);
	g_rtt_next_idx += 7U;
	data_pa[3] = reserve_delegated_granules(1U);

	for (unsigned int i = 0U; i < 4U; i++) {
		CHECK_TRUE(init_ripas_range(&ctx, ipa[i], ipa[i] + GRANULE_SIZE));
		CHECK_TRUE(map_data_page(&ctx, ipa[i], data_pa[i]));
	}

	cur_base = ipa[0];
	while (cur_base < top) {
		unsigned long copied;

		res = {};
		smc_rtt_data_unmap(ctx.rd, cur_base, top,
				   make_unmap_flags(RMI_ADDR_TYPE_LIST, 8UL),
				   (unsigned long)list_pa, &res);
		res = sro_complete_operation(res);

		CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
		CHECK_TRUE(res.x[1] > cur_base);
		CHECK_TRUE(res.x[1] <= top);

		copied = res.x[3];
		for (unsigned long i = 0UL; i < copied; i++) {
			CHECK_TRUE(next_ipa_idx < 4U);
			rdesc = read_list_entry(list_pa, (unsigned int)i);
			CHECK_EQUAL(data_pa[next_ipa_idx],
				    decode_single_oaddr_pa(rdesc));
			CHECK_EQUAL(1UL, decode_rdesc_count(rdesc));
			CHECK_EQUAL(RMI_PAGE_L3,
				    decode_rdesc_size(rdesc));
			CHECK_EQUAL(RMI_OP_MEM_DELEGATED,
				    decode_rdesc_state(rdesc));
			expect_data_granule_delegated(
				data_pa[next_ipa_idx]);
			expect_ipa_unassigned_destroyed(&ctx,
				ipa[next_ipa_idx]);
			next_ipa_idx++;
		}

		cur_base = res.x[1];
	}

	CHECK_EQUAL(4U, next_ipa_idx);
}

/*
 * Installs an L2 device block as the first entry in the requested range.
 * DATA_UNMAP must report RMI_ERROR_RTT at level 2 and leave the device
 * mapping intact.
 */
TEST(rtt_data_unmap_tests, l2_device_block_first_returns_rtt_error)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	return_code_t rc;

	CHECK_TRUE(create_data_rtt_ctx_l2_only(&ctx));
	CHECK_TRUE(install_assigned_dev_mapping(&ctx, TEST_DATA_IPA_BASE,
						TEST_NS_PA, 2L));

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, TEST_DATA_L2_BLOCK_TOP,
			   make_unmap_flags_single(), 0UL, &res);

	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_ERROR_RTT, rc.status);
	CHECK_EQUAL(2U, rc.index);
	CHECK_EQUAL(0UL, res.x[1]);
	expect_ipa_assigned_dev_dev(&ctx, TEST_DATA_IPA_BASE, 2L);
}

/*
 * Builds one L2 table entry containing data, an adjacent L2 device block,
 * and a following L2 data block. DATA_UNMAP should unmap only the first
 * data page, stop at the device block, and continue to reject from there.
 */
TEST(rtt_data_unmap_tests, l2_table_device_block_data_block_mixed)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	struct smc_result res2 = {};
	uintptr_t list_pa = reserve_list_granule();
	uintptr_t page_pa;
	uintptr_t block_pa;
	unsigned long dev_ipa = TEST_DATA_L2_BLOCK_TOP;
	unsigned long block_ipa = TEST_DATA_IPA_BASE +
				  2UL * TEST_DATA_L2_BLOCK_SIZE;
	unsigned long top = block_ipa + TEST_DATA_L2_BLOCK_SIZE;
	unsigned long rdesc;
	return_code_t rc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(create_data_l3_rtt(&ctx, block_ipa));

	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_IPA_BASE + GRANULE_SIZE));
	page_pa = reserve_delegated_granules(1U);
	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE, page_pa));

	CHECK_TRUE(install_assigned_dev_mapping(&ctx, dev_ipa,
						TEST_NS_PA_ALT, 2L));

	CHECK_TRUE(init_ripas_range(&ctx, block_ipa, top));
	block_pa = reserve_delegated_granules_l2_aligned(
				(unsigned int)S2TTES_PER_S2TT);
	CHECK_TRUE(map_data_pages(&ctx, block_ipa, block_pa,
				  (unsigned int)S2TTES_PER_S2TT));
	CHECK_TRUE(fold_to_l2(&ctx, block_ipa));

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags(RMI_ADDR_TYPE_LIST, 4UL),
			   (unsigned long)list_pa, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(dev_ipa, res.x[1]);
	CHECK_EQUAL(1UL, res.x[3]);

	rdesc = read_list_entry(list_pa, 0U);
	CHECK_EQUAL(page_pa, decode_single_oaddr_pa(rdesc));
	CHECK_EQUAL(1UL, decode_rdesc_count(rdesc));
	CHECK_EQUAL(RMI_PAGE_L3, decode_rdesc_size(rdesc));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(rdesc));

	expect_data_granule_delegated(page_pa);
	expect_ipa_unassigned_destroyed(&ctx, TEST_DATA_IPA_BASE);
	expect_ipa_assigned_dev_dev(&ctx, dev_ipa, 2L);
	expect_data_granules_data_state(block_pa, (unsigned int)S2TTES_PER_S2TT);

	smc_rtt_data_unmap(ctx.rd, dev_ipa, top,
			   make_unmap_flags_single(), 0UL, &res2);

	rc = unpack_return_code(res2.x[0]);
	CHECK_EQUAL(RMI_ERROR_RTT, rc.status);
	CHECK_EQUAL(2U, rc.index);
	CHECK_EQUAL(0UL, res2.x[1]);

	expect_ipa_assigned_dev_dev(&ctx, dev_ipa, 2L);
	expect_data_granules_data_state(block_pa, (unsigned int)S2TTES_PER_S2TT);
}

/* ------------------------------------------------------------------ */
/* ISR yield paths: pending work is completed through RMI_OP_CONTINUE. */
/* ------------------------------------------------------------------ */

#ifdef RMM_RTT_MAP_UNMAP_CHECK_ISR_EL1
/*
 * data_unmap_rtc_yield_keep_going
 *
 * Maps 6 contiguous L3 pages, primes the ISR to fire on the first
 * deferred-work IRQ check, verifies that the initial call returns
 * RMI_INCOMPLETE, then completes the operation with RMI_OP_CONTINUE.
 */
TEST(rtt_data_unmap_tests, data_unmap_rtc_yield_keep_going)
{
	static const unsigned int N = 6U;
	unsigned long top = TEST_DATA_IPA_BASE + (unsigned long)N * GRANULE_SIZE;
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;

	CHECK_TRUE(setup_and_map_pages(&ctx, TEST_DATA_IPA_BASE, top, N,
				       &data_base));

	prime_isr_yield();

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags_none(), 0UL, &res);

	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	expect_data_granules_data_state(data_base, N);

	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top, res.x[1]);

	expect_data_granules_delegated(data_base, N);
	for (unsigned int i = 0U; i < N; i++) {
		expect_ipa_unassigned_destroyed(
			&ctx,
			TEST_DATA_IPA_BASE + (unsigned long)i * GRANULE_SIZE);
	}
}

/*
 * data_unmap_rtc_yield_stamps_pending_state_then_continue
 *
 * Same setup as the keep-going test, but explicitly verifies the intermediate
 * TTE state before RMI_OP_CONTINUE performs the deferred TLBI and drains the
 * pending DATA granules.
 */
TEST(rtt_data_unmap_tests, data_unmap_rtc_yield_stamps_pending_state_then_continue)
{
	static const unsigned int N = 6U;
	unsigned long top = TEST_DATA_IPA_BASE + (unsigned long)N * GRANULE_SIZE;
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;
	unsigned int handle;

	CHECK_TRUE(setup_and_map_pages(&ctx, TEST_DATA_IPA_BASE, top, N,
				       &data_base));

	prime_isr_yield();

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags_none(), 0UL, &res);

	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	expect_data_granules_data_state(data_base, N);
	for (unsigned int i = 0U; i < N; i++) {
		unsigned long ipa = TEST_DATA_IPA_BASE +
				    (unsigned long)i * GRANULE_SIZE;
		unsigned long s2tte = read_data_ipa_raw_s2tte(&ctx, ipa);

		expect_ipa_unassigned_destroyed(&ctx, ipa);
		CHECK_TRUE(s2tte_drain_pending(s2tte));
		CHECK_TRUE(s2tte_tlbi_pending(s2tte));
	}

	handle = s2tte_drain_handle(
			read_data_ipa_raw_s2tte(&ctx, TEST_DATA_IPA_BASE));
	for (unsigned int i = 1U; i < N; i++) {
		unsigned long ipa = TEST_DATA_IPA_BASE +
				    (unsigned long)i * GRANULE_SIZE;
		unsigned long s2tte = read_data_ipa_raw_s2tte(&ctx, ipa);

		CHECK_EQUAL(handle, s2tte_drain_handle(s2tte));
	}

	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top, res.x[1]);
	expect_data_granules_delegated(data_base, N);
	for (unsigned int i = 0U; i < N; i++) {
		unsigned long ipa = TEST_DATA_IPA_BASE +
				    (unsigned long)i * GRANULE_SIZE;
		unsigned long s2tte = read_data_ipa_raw_s2tte(&ctx, ipa);

		expect_ipa_unassigned_destroyed(&ctx, ipa);
		CHECK_FALSE(s2tte_drain_pending(s2tte));
		CHECK_FALSE(s2tte_tlbi_pending(s2tte));
		CHECK_EQUAL(0U, s2tte_drain_handle(s2tte));
	}
}

/*
 * Delays the ISR until the TLBI-pending scan has completed, so the incomplete
 * return is caused by the IRQ check inside rtt_unmap_drain_pending().
 */
TEST(rtt_data_unmap_tests, data_unmap_yields_in_drain_phase)
{
	static const unsigned int N = 6U;
	unsigned long top = TEST_DATA_IPA_BASE + (unsigned long)N * GRANULE_SIZE;
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;

	CHECK_TRUE(setup_and_map_pages(&ctx, TEST_DATA_IPA_BASE, top, N,
				       &data_base));

	prime_isr_yield_in_drain();

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags_none(), 0UL, &res);

	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	expect_data_granules_data_state(data_base, N);
	for (unsigned int i = 0U; i < N; i++) {
		unsigned long ipa = TEST_DATA_IPA_BASE +
				    (unsigned long)i * GRANULE_SIZE;
		unsigned long s2tte = read_data_ipa_raw_s2tte(&ctx, ipa);

		CHECK_TRUE(s2tte_drain_pending(s2tte));
		CHECK_FALSE(s2tte_tlbi_pending(s2tte));
	}

	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top, res.x[1]);
	expect_data_granules_delegated(data_base, N);
	for (unsigned int i = 0U; i < N; i++) {
		expect_ipa_unassigned_destroyed(
			&ctx,
			TEST_DATA_IPA_BASE + (unsigned long)i * GRANULE_SIZE);
	}
}
#endif

/*
 * list_mode_pauses_on_level_change_then_unmaps_l2_block
 *
 * Maps one L3 page at TEST_DATA_IPA_BASE and an L2 block (via fold) at
 * TEST_DATA_L2_BLOCK_TOP. The first LIST unmap covering both 2MB regions
 * should:
 *   1. Process the L3 page (write one descriptor to the output list).
 *   2. Detect that the adjacent LLT maps at L2 (different block size).
 *   3. Pause cleanly: return RMI_SUCCESS with out_top == TEST_DATA_L2_BLOCK_TOP.
 *
 * A follow-up SINGLE unmap from the returned out_top then unmaps the L2 block.
 *
 * The L2 block is built by mapping a full L3 table with contiguous PAs and
 * folding it, matching the other L2 block tests.
 */
TEST(rtt_data_unmap_tests, list_mode_pauses_on_level_change_then_unmaps_l2_block)
{
	unsigned long top = TEST_DATA_L2_BLOCK_TOP + TEST_DATA_L2_BLOCK_SIZE;
	struct test_data_ctx ctx;
	struct smc_result res = {};
	struct smc_result res2 = {};
	uintptr_t list_pa = reserve_list_granule();
	uintptr_t page_pa = 0UL;
	uintptr_t block_pa = 0UL;
	uintptr_t rtt_l3_blk;
	unsigned long rdesc;

	/*
	 * create_data_rtt_ctx creates L1+L2+L3 for TEST_DATA_IPA_BASE.
	 * Add a second L3 RTT covering TEST_DATA_L2_BLOCK_TOP so that the
	 * 512 L3 pages can be mapped and then folded into an L2 block.
	 */
	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	rtt_l3_blk = reserve_delegated_granules(1U);
	CHECK_EQUAL(RMI_SUCCESS,
		    smc_rtt_create(ctx.rd, rtt_l3_blk,
				   TEST_DATA_L2_BLOCK_TOP, 3UL));

	/* Map one L3 page at TEST_DATA_IPA_BASE */
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_IPA_BASE + GRANULE_SIZE));
	page_pa = reserve_delegated_granules(1U);
	CHECK_TRUE(map_data_page(&ctx, TEST_DATA_IPA_BASE, page_pa));

	/* Map 512 L3 pages at TEST_DATA_L2_BLOCK_TOP, then fold to L2. */
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_L2_BLOCK_TOP, top));
	block_pa = reserve_delegated_granules_l2_aligned(
				(unsigned int)S2TTES_PER_S2TT);
	CHECK_TRUE(map_data_pages(&ctx, TEST_DATA_L2_BLOCK_TOP, block_pa,
				  (unsigned int)S2TTES_PER_S2TT));
	CHECK_TRUE(fold_to_l2(&ctx, TEST_DATA_L2_BLOCK_TOP));

	/* LIST unmap covering L3 page range then L2 block range */
	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags(RMI_ADDR_TYPE_LIST, 2UL),
			   (unsigned long)list_pa, &res);
	res = sro_complete_operation(res);

	/* Level-change gate pauses before the L2 LLT */
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_L2_BLOCK_TOP, res.x[1]);
	/* One L3-page descriptor written to the output list */
	CHECK_EQUAL(1UL, res.x[3]);

	rdesc = read_list_entry(list_pa, 0U);
	CHECK_EQUAL(page_pa, decode_single_oaddr_pa(rdesc));
	CHECK_EQUAL(1UL, decode_rdesc_count(rdesc));
	CHECK_EQUAL(RMI_PAGE_L3, decode_rdesc_size(rdesc));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(rdesc));

	/* L3 page is unmapped: granule to DELEGATED, entry to unassigned_destroyed. */
	expect_data_granule_delegated(page_pa);
	expect_ipa_unassigned_destroyed(&ctx, TEST_DATA_IPA_BASE);

	/* L2 block is NOT yet unmapped: all 512 granules remain in DATA state */
	expect_data_granules_data_state(block_pa, (unsigned int)S2TTES_PER_S2TT);

	smc_rtt_data_unmap(ctx.rd, res.x[1], top,
			   make_unmap_flags_single(), 0UL, &res2);
	res2 = sro_complete_operation(res2);

	CHECK_EQUAL(RMI_SUCCESS, res2.x[0]);
	CHECK_EQUAL(top, res2.x[1]);
	CHECK_EQUAL(block_pa, decode_single_oaddr_pa(res2.x[2]));
	CHECK_EQUAL(1UL, decode_rdesc_count(res2.x[2]));
	CHECK_EQUAL(RMI_BLOCK_L2, decode_rdesc_size(res2.x[2]));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED, decode_rdesc_state(res2.x[2]));

	expect_data_granules_delegated(block_pa, (unsigned int)S2TTES_PER_S2TT);
}

/*
 * DATA_UNMAP can make no descriptor progress after skipping non-live L2
 * entries and then stopping at a table descriptor. The returned out_top must
 * be the table IPA.
 */
TEST(rtt_data_unmap_tests, no_progress_after_skipping_holes_stops_at_table)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	unsigned long table_ipa = TEST_DATA_IPA_BASE +
				  (2UL * TEST_DATA_L2_BLOCK_SIZE);
	unsigned long top = table_ipa + TEST_DATA_L2_BLOCK_SIZE;

	CHECK_TRUE(create_data_rtt_ctx_l2_only(&ctx));
	CHECK_TRUE(create_data_l3_rtt(&ctx, table_ipa));

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags_none(), 0UL, &res);
	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(table_ipa, res.x[1]);
	CHECK_EQUAL(0UL, res.x[2]);
	CHECK_EQUAL(0UL, res.x[3]);
}

#ifdef RMM_RTT_MAP_UNMAP_CHECK_ISR_EL1
/*
 * list_mode_yield_flushes_partial_list
 *
 * LIST-mode counterpart of data_unmap_rtc_yield_keep_going. Verifies
 * that an ISR-triggered yield in LIST mode is completed through
 * RMI_OP_CONTINUE.
 */
TEST(rtt_data_unmap_tests, list_mode_yield_flushes_partial_list)
{
	static const unsigned int N = 6U;
	unsigned long top = TEST_DATA_IPA_BASE + (unsigned long)N * GRANULE_SIZE;
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;
	uintptr_t list_pa = reserve_list_granule();

	CHECK_TRUE(setup_and_map_pages(&ctx, TEST_DATA_IPA_BASE, top, N,
				       &data_base));

	prime_isr_yield();

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags(RMI_ADDR_TYPE_LIST,
					   (unsigned long)ADDR_LIST_MAX_RANGES),
			   (unsigned long)list_pa, &res);

	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);

	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top, res.x[1]);

	expect_data_granules_delegated(data_base, N);
	for (unsigned int i = 0U; i < N; i++) {
		expect_ipa_unassigned_destroyed(
			&ctx,
			TEST_DATA_IPA_BASE + (unsigned long)i * GRANULE_SIZE);
	}
}

/*
 * yields_twice_then_completes
 *
 * Verifies that the ISR-yield path can be continued multiple times.
 * ISR is primed to fire on the first two read_isr_el1() calls; the
 * final RMI_OP_CONTINUE sees ISR == 0 and completes the drain.
 */
TEST(rtt_data_unmap_tests, yields_twice_then_completes)
{
	static const unsigned int N = 6U;
	unsigned long top = TEST_DATA_IPA_BASE + (unsigned long)N * GRANULE_SIZE;
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;

	CHECK_TRUE(setup_and_map_pages(&ctx, TEST_DATA_IPA_BASE, top, N,
				       &data_base));

	prime_isr_yield_twice();

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags_none(), 0UL, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);

	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top, res.x[1]);

	expect_data_granules_delegated(data_base, N);
	for (unsigned int i = 0U; i < N; i++) {
		expect_ipa_unassigned_destroyed(
			&ctx,
			TEST_DATA_IPA_BASE + (unsigned long)i * GRANULE_SIZE);
	}
}

/* ------------------------------------------------------------------ */
/* Drain-pending SW bit: stamp / clear / consumer-gate races          */
/* ------------------------------------------------------------------ */

/*
 * drain_pending_mark_set_after_yield_cleared_after_continue
 *
 * Verifies the SW drain-pending lifecycle observable in the TTE:
 *   1. Maps N pages, primes an ISR yield.
 *   2. After the yield (RMI_INCOMPLETE), every IPA is unassigned_destroyed
 *      and carries the drain-pending SW bit + a consistent handle.
 *   3. After RMI_OP_CONTINUE completes the drain, the SW bits are cleared
 *      on every IPA while the architectural state remains
 *      unassigned_destroyed.
 */
TEST(rtt_data_unmap_tests, drain_pending_mark_set_after_yield_cleared_after_continue)
{
	static const unsigned int N = 6U;
	unsigned long top = TEST_DATA_IPA_BASE + (unsigned long)N * GRANULE_SIZE;
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base = 0UL;
	unsigned int handle;

	CHECK_TRUE(setup_and_map_pages(&ctx, TEST_DATA_IPA_BASE, top, N,
				       &data_base));

	prime_isr_yield();

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags_none(), 0UL, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);

	/* Sweep already converted every entry; the drain has not run yet. */
	expect_data_granules_data_state(data_base, N);
	for (unsigned int i = 0U; i < N; i++) {
		unsigned long ipa = TEST_DATA_IPA_BASE +
				    (unsigned long)i * GRANULE_SIZE;
		unsigned long s2tte = read_data_ipa_raw_s2tte(&ctx, ipa);

		expect_ipa_unassigned_destroyed(&ctx, ipa);
		CHECK_TRUE(s2tte_drain_pending(s2tte));
	}

	/* Handle must be consistent across all stamped entries. */
	handle = s2tte_drain_handle(
			read_data_ipa_raw_s2tte(&ctx, TEST_DATA_IPA_BASE));
	for (unsigned int i = 1U; i < N; i++) {
		unsigned long ipa = TEST_DATA_IPA_BASE +
				    (unsigned long)i * GRANULE_SIZE;
		unsigned long s2tte = read_data_ipa_raw_s2tte(&ctx, ipa);

		CHECK_EQUAL(handle, s2tte_drain_handle(s2tte));
	}

	res = sro_complete_operation(res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top, res.x[1]);

	expect_data_granules_delegated(data_base, N);
	for (unsigned int i = 0U; i < N; i++) {
		unsigned long ipa = TEST_DATA_IPA_BASE +
				    (unsigned long)i * GRANULE_SIZE;
		unsigned long s2tte = read_data_ipa_raw_s2tte(&ctx, ipa);

		expect_ipa_unassigned_destroyed(&ctx, ipa);
		CHECK_FALSE(s2tte_drain_pending(s2tte));
		CHECK_EQUAL(0U, s2tte_drain_handle(s2tte));
	}
}

/*
 * data_create_blocked_while_drain_pending_then_succeeds
 *
 * Race-style test for the DATA_CREATE consumer gate:
 *   1. Unmap leaves every IPA stamped drain-pending mid-yield.
 *   2. RMI_DATA_MAP (the public path that funnels into data_create()) on a
 *      stamped IPA must return RMI_BUSY without changing system state.
 *   3. The fresh delegated granule remains DELEGATED across the failed
 *      attempt (consumer gate does not consume it).
 *   4. After RMI_OP_CONTINUE drains and clears the marks, the retry
 *      succeeds.
 */
TEST(rtt_data_unmap_tests, data_create_blocked_while_drain_pending_then_succeeds)
{
	static const unsigned int N = 4U;
	unsigned long top = TEST_DATA_IPA_BASE + (unsigned long)N * GRANULE_SIZE;
	struct test_data_ctx ctx;
	struct smc_result res = {};
	struct smc_result res_create = {};
	uintptr_t data_base = 0UL;
	uintptr_t retry_pa;
	uintptr_t blocked_pa;
	unsigned long retry_ipa = TEST_DATA_IPA_BASE;
	unsigned long desc;

	CHECK_TRUE(setup_and_map_pages(&ctx, TEST_DATA_IPA_BASE, top, N,
				       &data_base));

	prime_isr_yield();

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, top,
			   make_unmap_flags_none(), 0UL, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	CHECK_TRUE(s2tte_drain_pending(
		read_data_ipa_raw_s2tte(&ctx, retry_ipa)));

	/*
	 * Attempt DATA_MAP on the drain-pending IPA. Must report RMI_BUSY
	 * and leave the fresh granule DELEGATED.
	 */
	blocked_pa = reserve_delegated_granules(1U);
	desc = INPLACE(RMI_ADDR_RDESC_4K_CNT, 1UL) |
	       INPLACE(RMI_ADDR_RDESC_4K_ADDR,
		       (unsigned long)blocked_pa >> GRANULE_SHIFT);
	smc_rtt_data_map(ctx.rd, retry_ipa, retry_ipa + GRANULE_SIZE,
			 RMI_ADDR_TYPE_SINGLE, desc, &res_create);
	CHECK_EQUAL(RMI_BUSY, res_create.x[0]);
	expect_data_granule_delegated(blocked_pa);
	expect_ipa_unassigned_destroyed(&ctx, retry_ipa);
	CHECK_TRUE(s2tte_drain_pending(
		read_data_ipa_raw_s2tte(&ctx, retry_ipa)));

	/* Complete the SRO; drain clears all stamps. */
	res = sro_complete_operation(res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	expect_data_granules_delegated(data_base, N);
	CHECK_FALSE(s2tte_drain_pending(
		read_data_ipa_raw_s2tte(&ctx, retry_ipa)));

	/* Retry now succeeds. */
	retry_pa = reserve_delegated_granules(1U);
	desc = INPLACE(RMI_ADDR_RDESC_4K_CNT, 1UL) |
	       INPLACE(RMI_ADDR_RDESC_4K_ADDR,
		       (unsigned long)retry_pa >> GRANULE_SHIFT);
	(void)memset(&res_create, 0, sizeof(res_create));
	smc_rtt_data_map(ctx.rd, retry_ipa, retry_ipa + GRANULE_SIZE,
			 RMI_ADDR_TYPE_SINGLE, desc, &res_create);
	CHECK_EQUAL(RMI_SUCCESS, res_create.x[0]);
	CHECK_EQUAL(retry_ipa + GRANULE_SIZE, res_create.x[1]);
	expect_data_granule_data_state(retry_pa);
	expect_data_granule_delegated(blocked_pa);
}

/*
 * data_create_blocked_only_on_stamped_ipa
 *
 * Cross-check that the gate is per-entry: while one IPA is drain-pending,
 * DATA_MAP on an unrelated, never-mapped IPA in the same realm proceeds
 * normally (its TTE is unassigned_empty with no SW bits).
 */
TEST(rtt_data_unmap_tests, data_create_blocked_only_on_stamped_ipa)
{
	static const unsigned int N = 2U;
	unsigned long unmap_top = TEST_DATA_IPA_BASE +
				  (unsigned long)N * GRANULE_SIZE;
	unsigned long free_ipa = TEST_DATA_IPA_BASE +
				 4UL * GRANULE_SIZE;
	struct test_data_ctx ctx;
	struct smc_result res = {};
	struct smc_result res_create = {};
	uintptr_t data_base = 0UL;
	uintptr_t free_pa;
	unsigned long desc;

	CHECK_TRUE(setup_and_map_pages(&ctx, TEST_DATA_IPA_BASE, unmap_top, N,
				       &data_base));

	/*
	 * Initialise an additional protected IPA to RIPAS=RAM so DATA_MAP
	 * has a legitimate landing slot outside the unmap range.
	 */
	CHECK_TRUE(init_ripas_range(&ctx, free_ipa, free_ipa + GRANULE_SIZE));

	prime_isr_yield();

	smc_rtt_data_unmap(ctx.rd, TEST_DATA_IPA_BASE, unmap_top,
			   make_unmap_flags_none(), 0UL, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	CHECK_TRUE(s2tte_drain_pending(
		read_data_ipa_raw_s2tte(&ctx, TEST_DATA_IPA_BASE)));
	CHECK_FALSE(s2tte_drain_pending(
		read_data_ipa_raw_s2tte(&ctx, free_ipa)));

	free_pa = reserve_delegated_granules(1U);
	desc = INPLACE(RMI_ADDR_RDESC_4K_CNT, 1UL) |
	       INPLACE(RMI_ADDR_RDESC_4K_ADDR,
		       (unsigned long)free_pa >> GRANULE_SHIFT);
	smc_rtt_data_map(ctx.rd, free_ipa, free_ipa + GRANULE_SIZE,
			 RMI_ADDR_TYPE_SINGLE, desc, &res_create);
	CHECK_EQUAL(RMI_SUCCESS, res_create.x[0]);
	expect_data_granule_data_state(free_pa);
	expect_ipa_assigned_ram(&ctx, free_ipa);

	res = sro_complete_operation(res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	expect_data_granules_delegated(data_base, N);
}
#endif

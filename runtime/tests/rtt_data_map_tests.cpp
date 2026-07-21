/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

#include "rtt_data_test_helpers.h"

TEST_GROUP(rtt_data_map_tests) {
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

static void smc_rtt_data_map_complete(unsigned long rd,
				      unsigned long base,
				      unsigned long top,
				      unsigned long flags,
				      unsigned long oaddr,
				      struct smc_result *res)
{
	smc_rtt_data_map(rd, base, top, flags, oaddr, res);
	*res = sro_complete_operation(*res);
}

/* ------------------------------------------------------------------ *
 * DATA_MAP_INIT input validation                                     *
 * ------------------------------------------------------------------ */

TEST(rtt_data_map_tests, data_map_init_rejects_rd_as_data)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t src;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	src = reserve_list_granule();

	smc_rtt_data_map_init(ctx.rd, ctx.rd, TEST_DATA_IPA_BASE, src,
			      RMI_NO_MEASURE_CONTENT, &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

TEST(rtt_data_map_tests, data_map_init_rejects_leaf_rtt_as_data)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t src;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	src = reserve_list_granule();

	smc_rtt_data_map_init(ctx.rd, ctx.rtt_l3, TEST_DATA_IPA_BASE, src,
			      RMI_NO_MEASURE_CONTENT, &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ------------------------------------------------------------------ *
 * Successful mappings                                                *
 * ------------------------------------------------------------------ */

/*
 * Map one L3 data page from a single descriptor and verify the IPA maps to
 * the requested delegated PA.
 */
TEST(rtt_data_map_tests, l3_single_page_single_descriptor_happy_path)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;
	unsigned long desc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_PAGE_TOP));

	data_pa = reserve_delegated_granules(1U);
	desc = make_data_map_desc(1UL, data_pa);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  desc, &res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_PAGE_TOP, res.x[1]);
	expect_data_granule_data_state(data_pa);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE, data_pa);
}

/*
 * Map two contiguous L3 data pages from one descriptor and check that both
 * output PAs are consumed in order.
 */
TEST(rtt_data_map_tests, l3_single_descriptor_maps_two_contiguous_pages)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base;
	unsigned long top = TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE;
	unsigned long desc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, top));

	data_base = reserve_delegated_granules(2U);
	desc = make_data_map_desc(2UL, data_base);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE, top,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  desc, &res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top, res.x[1]);
	expect_data_granules_data_state(data_base, 2U);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE, data_base);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE + GRANULE_SIZE,
				      data_base + GRANULE_SIZE);
}

/*
 * Map two L3 pages from a descriptor list where the backing PAs are not
 * contiguous.
 */
TEST(rtt_data_map_tests, l3_list_maps_non_contiguous_data_pages)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t list_pa = reserve_list_granule();
	uintptr_t data0;
	uintptr_t data1;
	unsigned long top = TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, top));

	data0 = reserve_delegated_granules(1U);
	g_rtt_next_idx += 3U;
	data1 = reserve_delegated_granules(1U);

	write_list_input_entry(list_pa, 0U, make_data_map_desc(1UL, data0));
	write_list_input_entry(list_pa, 1U, make_data_map_desc(1UL, data1));

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE, top,
				  make_data_map_flags(RMI_ADDR_TYPE_LIST, 2UL),
				  (unsigned long)list_pa, &res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(top, res.x[1]);
	expect_data_granule_data_state(data0);
	expect_data_granule_data_state(data1);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE, data0);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE + GRANULE_SIZE,
				      data1);
}

/*
 * Map the first two L3 pages from a list, then re-map them idempotently while
 * mapping the third page from the third list entry.
 */
TEST(rtt_data_map_tests, l3_list_maps_third_after_two_idempotent_entries)
{
	struct test_data_ctx ctx;
	struct smc_result first_res = {};
	struct smc_result second_res = {};
	uintptr_t list_pa = reserve_list_granule();
	uintptr_t data0;
	uintptr_t data1;
	uintptr_t data2;
	unsigned long ipa1 = TEST_DATA_IPA_BASE + GRANULE_SIZE;
	unsigned long ipa2 = TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE;
	unsigned long first_top = TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE;
	unsigned long top = TEST_DATA_IPA_BASE + 3UL * GRANULE_SIZE;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, top));

	data0 = reserve_delegated_granules(1U);
	g_rtt_next_idx += 2U;
	data1 = reserve_delegated_granules(1U);
	g_rtt_next_idx += 4U;
	data2 = reserve_delegated_granules(1U);

	write_list_input_entry(list_pa, 0U, make_data_map_desc(1UL, data0));
	write_list_input_entry(list_pa, 1U, make_data_map_desc(1UL, data1));

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE, first_top,
				  make_data_map_flags(RMI_ADDR_TYPE_LIST, 2UL),
				  (unsigned long)list_pa, &first_res);

	CHECK_EQUAL(RMI_SUCCESS, first_res.x[0]);
	CHECK_EQUAL(first_top, first_res.x[1]);
	expect_data_granule_data_state(data0);
	expect_data_granule_data_state(data1);
	expect_data_granule_delegated(data2);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE, data0);
	expect_ipa_assigned_ram_to_pa(&ctx, ipa1, data1);
	expect_ipa_unassigned_no_drain(&ctx, ipa2);

	write_list_input_entry(list_pa, 2U, make_data_map_desc(1UL, data2));

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE, top,
				  make_data_map_flags(RMI_ADDR_TYPE_LIST, 3UL),
				  (unsigned long)list_pa, &second_res);

	CHECK_EQUAL(RMI_SUCCESS, second_res.x[0]);
	CHECK_EQUAL(top, second_res.x[1]);
	expect_data_granule_data_state(data0);
	expect_data_granule_data_state(data1);
	expect_data_granule_data_state(data2);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE, data0);
	expect_ipa_assigned_ram_to_pa(&ctx, ipa1, data1);
	expect_ipa_assigned_ram_to_pa(&ctx, ipa2, data2);
}

/*
 * Map an L2 block from a single descriptor and verify the whole block becomes
 * assigned RAM.
 */
TEST(rtt_data_map_tests, l2_block_single_descriptor_happy_path)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base;
	unsigned long desc;

	CHECK_TRUE(create_data_rtt_ctx_l2_only(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_L2_BLOCK_TOP));

	data_base = reserve_delegated_granules_l2_aligned(
				(unsigned int)S2TTES_PER_S2TT);
	desc = make_data_map_desc(1UL, data_base, RMI_BLOCK_L2);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_L2_BLOCK_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  desc, &res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_L2_BLOCK_TOP, res.x[1]);
	expect_data_granules_data_state(data_base,
					(unsigned int)S2TTES_PER_S2TT);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE, data_base, 2L);
}

/*
 * Re-map an IPA to the same PA and verify the operation remains idempotent.
 */
TEST(rtt_data_map_tests, already_mapped_same_pa_is_idempotent)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	struct smc_result res2 = {};
	uintptr_t data_pa;
	unsigned long desc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_PAGE_TOP));

	data_pa = reserve_delegated_granules(1U);
	desc = make_data_map_desc(1UL, data_pa);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  desc, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  desc, &res2);

	CHECK_EQUAL(RMI_SUCCESS, res2.x[0]);
	CHECK_EQUAL(TEST_DATA_PAGE_TOP, res2.x[1]);
	expect_data_granule_data_state(data_pa);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE, data_pa);
}

/* ------------------------------------------------------------------ *
 * Partial progress                                                   *
 * ------------------------------------------------------------------ */

#ifdef RMM_RTT_MAP_UNMAP_CHECK_ISR_EL1
/*
 * If DATA_MAP sees a pending IRQ before popping the first descriptor, report
 * zero progress as success with out_top equal to base.
 */
TEST(rtt_data_map_tests, irq_before_first_descriptor_reports_base_out_top)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;
	unsigned long desc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_PAGE_TOP));

	data_pa = reserve_delegated_granules(1U);
	desc = make_data_map_desc(1UL, data_pa);
	res.x[1] = TEST_DATA_PAGE_TOP;

	prime_isr_yield_before_data_map_pop();

	smc_rtt_data_map(ctx.rd, TEST_DATA_IPA_BASE, TEST_DATA_PAGE_TOP,
			 make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
			 desc, &res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_IPA_BASE, res.x[1]);
	expect_data_granule_delegated(data_pa);
	expect_ipa_unassigned_no_drain(&ctx, TEST_DATA_IPA_BASE);
}
#endif

/*
 * Stop a multi-page single descriptor at the requested top IPA without
 * consuming the next delegated granule.
 */
TEST(rtt_data_map_tests, single_descriptor_count_stops_at_requested_top)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base;
	unsigned long desc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_PAGE_TOP));

	data_base = reserve_delegated_granules(2U);
	desc = make_data_map_desc(2UL, data_base);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  desc, &res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_PAGE_TOP, res.x[1]);
	expect_data_granule_data_state(data_base);
	expect_data_granule_delegated(data_base + GRANULE_SIZE);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE, data_base);
}

/*
 * Stop cleanly after progress when a list descriptor changes translation
 * level before the requested top IPA.
 */
TEST(rtt_data_map_tests, list_level_change_after_progress_stops_cleanly)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t list_pa = reserve_list_granule();
	uintptr_t data0;
	uintptr_t data1;
	unsigned long top = TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, top));

	data0 = reserve_delegated_granules(1U);
	data1 = reserve_delegated_granules_l2_aligned(1U);

	write_list_input_entry(list_pa, 0U, make_data_map_desc(1UL, data0));
	write_list_input_entry(list_pa, 1U,
			       make_data_map_desc(1UL, data1, RMI_BLOCK_L2));

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE, top,
				  make_data_map_flags(RMI_ADDR_TYPE_LIST, 2UL),
				  (unsigned long)list_pa, &res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_IPA_BASE + GRANULE_SIZE, res.x[1]);
	expect_data_granule_data_state(data0);
	expect_data_granule_delegated(data1);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE, data0);
}

/*
 * Stop cleanly after progress when a later list descriptor has the wrong
 * memory state. The first descriptor gets past the initial input validator;
 * the second descriptor exercises the per-block descriptor-state failure path.
 */
TEST(rtt_data_map_tests, list_state_change_after_progress_stops_cleanly)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t list_pa = reserve_list_granule();
	uintptr_t data0;
	uintptr_t data1;
	unsigned long top = TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE, top));

	data0 = reserve_delegated_granules(1U);
	data1 = reserve_delegated_granules(1U);

	write_list_input_entry(list_pa, 0U, make_data_map_desc(1UL, data0));
	write_list_input_entry(list_pa, 1U,
			       make_data_map_desc(1UL, data1, RMI_PAGE_L3,
						  RMI_OP_MEM_UNDELEGATED));

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE, top,
				  make_data_map_flags(RMI_ADDR_TYPE_LIST, 2UL),
				  (unsigned long)list_pa, &res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_IPA_BASE + GRANULE_SIZE, res.x[1]);
	expect_data_granule_data_state(data0);
	expect_data_granule_delegated(data1);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE, data0);
}

/*
 * Stop at the leaf RTT boundary even when the descriptor covers IPA beyond
 * the initialized leaf table.
 */
TEST(rtt_data_map_tests, map_stops_at_leaf_rtt_boundary)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base;
	unsigned long base = TEST_DATA_L2_BLOCK_TOP - GRANULE_SIZE;
	unsigned long top = base + 2UL * GRANULE_SIZE;
	unsigned long desc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, base, TEST_DATA_L2_BLOCK_TOP));

	data_base = reserve_delegated_granules(2U);
	desc = make_data_map_desc(2UL, data_base);

	smc_rtt_data_map_complete(ctx.rd, base, top,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  desc, &res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_L2_BLOCK_TOP, res.x[1]);
	expect_data_granule_data_state(data_base);
	expect_data_granule_delegated(data_base + GRANULE_SIZE);
	expect_ipa_assigned_ram_to_pa(&ctx, base, data_base);
}

/* ------------------------------------------------------------------ *
 * Input validation and RTT errors                                    *
 * ------------------------------------------------------------------ */

/*
 * Reject an RD address that is not granule-aligned and leave the data granule
 * delegated.
 */
TEST(rtt_data_map_tests, rd_unaligned)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	data_pa = reserve_delegated_granules(1U);

	smc_rtt_data_map_complete(ctx.rd + 1UL, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  make_data_map_desc(1UL, data_pa), &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(data_pa);
}

/*
 * Reject an RD argument that names a granule in the wrong state.
 */
TEST(rtt_data_map_tests, rd_wrong_state)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	data_pa = reserve_delegated_granules(1U);

	smc_rtt_data_map_complete(ctx.rtt_l0, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  make_data_map_desc(1UL, data_pa), &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(data_pa);
}

/*
 * Reject DATA_MAP when the Realm is not in NEW or ACTIVE state.
 */
TEST(rtt_data_map_tests, realm_state_must_be_new_or_active)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	force_realm_state(&ctx, REALM_SYSTEM_OFF);
	data_pa = reserve_delegated_granules(1U);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  make_data_map_desc(1UL, data_pa), &res);

	CHECK_EQUAL(RMI_ERROR_REALM, res.x[0]);
	expect_data_granule_delegated(data_pa);
}

/*
 * Reject a base IPA outside the protected address range.
 */
TEST(rtt_data_map_tests, base_outside_par)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	data_pa = reserve_delegated_granules(1U);

	smc_rtt_data_map_complete(ctx.rd, TEST_PAR_SIZE,
				  TEST_PAR_SIZE + GRANULE_SIZE,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  make_data_map_desc(1UL, data_pa), &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(data_pa);
}

/*
 * Reject a base IPA that is not granule-aligned.
 */
TEST(rtt_data_map_tests, base_unaligned)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	data_pa = reserve_delegated_granules(1U);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE + 1UL,
				  TEST_DATA_PAGE_TOP + 1UL,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  make_data_map_desc(1UL, data_pa), &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(data_pa);
}

/*
 * Reject an empty IPA range where top equals base.
 */
TEST(rtt_data_map_tests, top_equal_base)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	data_pa = reserve_delegated_granules(1U);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_IPA_BASE,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  make_data_map_desc(1UL, data_pa), &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(data_pa);
}

/*
 * Reject DATA_MAP when the output address type is NONE.
 */
TEST(rtt_data_map_tests, invalid_oaddr_type_none)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	data_pa = reserve_delegated_granules(1U);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_NONE),
				  make_data_map_desc(1UL, data_pa), &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(data_pa);
}

/*
 * Reject DATA_MAP when the output address type encoding is reserved.
 */
TEST(rtt_data_map_tests, invalid_oaddr_type_reserved)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;
	unsigned long flags = INPLACE(RMI_RTT_PROT_MAP_FLAGS_OADDR_TYPE, 3UL);

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	data_pa = reserve_delegated_granules(1U);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP, flags,
				  make_data_map_desc(1UL, data_pa), &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(data_pa);
}

/*
 * Reject list mode when the descriptor count is zero.
 */
TEST(rtt_data_map_tests, list_count_zero_is_invalid)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t list_pa = reserve_list_granule();
	uintptr_t data_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	data_pa = reserve_delegated_granules(1U);
	write_list_input_entry(list_pa, 0U, make_data_map_desc(1UL, data_pa));

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_LIST, 0UL),
				  (unsigned long)list_pa, &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(data_pa);
}

/*
 * Reject list mode when the descriptor-list address is not granule-aligned.
 */
TEST(rtt_data_map_tests, list_oaddr_must_be_aligned)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t list_pa = reserve_list_granule();
	uintptr_t data_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	data_pa = reserve_delegated_granules(1U);
	write_list_input_entry(list_pa, 0U, make_data_map_desc(1UL, data_pa));

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_LIST, 1UL),
				  (unsigned long)list_pa + 1UL, &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(data_pa);
}

/*
 * Reject list mode when the descriptor-list address does not name NS memory.
 */
TEST(rtt_data_map_tests, list_oaddr_must_reference_ns_memory)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t delegated_list_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	delegated_list_pa = reserve_delegated_granules(1U);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_LIST, 1UL),
				  (unsigned long)delegated_list_pa, &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(delegated_list_pa);
}

/*
 * Reject a descriptor whose target granule state is not DELEGATED.
 */
TEST(rtt_data_map_tests, descriptor_must_be_delegated_state)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;
	unsigned long desc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	data_pa = reserve_delegated_granules(1U);
	desc = make_data_map_desc(1UL, data_pa, RMI_PAGE_L3,
				  RMI_OP_MEM_UNDELEGATED);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  desc, &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(data_pa);
}

/*
 * Reject list mode when the first descriptor's memory state is not DELEGATED.
 */
TEST(rtt_data_map_tests, list_first_descriptor_must_be_delegated_state)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t list_pa = reserve_list_granule();
	uintptr_t data_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	data_pa = reserve_delegated_granules(1U);
	write_list_input_entry(list_pa, 0U,
			       make_data_map_desc(1UL, data_pa, RMI_PAGE_L3,
						  RMI_OP_MEM_UNDELEGATED));

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_LIST, 1UL),
				  (unsigned long)list_pa, &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(data_pa);
}

/*
 * Reject a descriptor with a zero granule count.
 */
TEST(rtt_data_map_tests, empty_descriptor_is_invalid)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	data_pa = reserve_delegated_granules(1U);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  make_data_map_desc(0UL, data_pa), &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(data_pa);
}

/*
 * Reject an L2 block descriptor when the requested IPA range is only L3 sized.
 */
TEST(rtt_data_map_tests, l2_map_requires_l2_sized_range)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base;
	return_code_t rc;

	CHECK_TRUE(create_data_rtt_ctx_l2_only(&ctx));
	data_base = reserve_delegated_granules_l2_aligned(1U);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  make_data_map_desc(1UL, data_base,
						     RMI_BLOCK_L2),
				  &res);

	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_ERROR_RTT, rc.status);
	CHECK_EQUAL(2U, rc.index);
	expect_data_granule_delegated(data_base);
}

/*
 * Report an RTT error when an L3 descriptor targets an IPA without a level 3
 * leaf RTT.
 */
TEST(rtt_data_map_tests, l3_map_requires_leaf_rtt)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;
	return_code_t rc;

	CHECK_TRUE(create_data_rtt_ctx_l2_only(&ctx));
	data_pa = reserve_delegated_granules(1U);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  make_data_map_desc(1UL, data_pa),
				  &res);

	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_ERROR_RTT, rc.status);
	CHECK_EQUAL(2U, rc.index);
	expect_data_granule_delegated(data_pa);
	expect_ipa_unassigned_no_drain(&ctx, TEST_DATA_IPA_BASE);
}

/*
 * Reject an L2 block descriptor whose PA is not aligned to an L2 block.
 */
TEST(rtt_data_map_tests, l2_map_rejects_misaligned_pa)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;

	CHECK_TRUE(create_data_rtt_ctx_l2_only(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_L2_BLOCK_TOP));
	data_pa = reserve_delegated_granules(1U);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_L2_BLOCK_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  make_data_map_desc(1UL, data_pa,
						     RMI_BLOCK_L2),
				  &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(data_pa);
}

/*
 * Reject a PA that exceeds the non-LPA2 PA width.
 */
TEST(rtt_data_map_tests, pa_must_fit_without_lpa2)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	unsigned long high_pa = 1UL << S2TT_MAX_PA_BITS;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_PAGE_TOP));

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  make_data_map_desc(1UL, high_pa), &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/*
 * Report an RTT error when an IPA is already mapped to a different PA.
 */
TEST(rtt_data_map_tests, existing_mapping_to_different_pa_returns_rtt_error)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	struct smc_result res2 = {};
	uintptr_t data0;
	uintptr_t data1;
	return_code_t rc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_PAGE_TOP));

	data0 = reserve_delegated_granules(1U);
	data1 = reserve_delegated_granules(1U);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  make_data_map_desc(1UL, data0), &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_PAGE_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  make_data_map_desc(1UL, data1), &res2);

	rc = unpack_return_code(res2.x[0]);
	CHECK_EQUAL(RMI_ERROR_RTT, rc.status);
	CHECK_EQUAL(S2TT_PAGE_LEVEL, rc.index);
	expect_data_granule_data_state(data0);
	expect_data_granule_delegated(data1);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE, data0);
}

/*
 * Report an RTT error when an L2 map collides with an existing L3 RTT.
 */
TEST(rtt_data_map_tests, l2_map_rejects_existing_l3_table)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base;
	return_code_t rc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_L2_BLOCK_TOP));
	data_base = reserve_delegated_granules_l2_aligned(
				(unsigned int)S2TTES_PER_S2TT);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_L2_BLOCK_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  make_data_map_desc(1UL, data_base,
						     RMI_BLOCK_L2),
				  &res);

	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_ERROR_RTT, rc.status);
	CHECK_EQUAL(2U, rc.index);
	expect_data_granules_delegated(data_base,
				       (unsigned int)S2TTES_PER_S2TT);
}

/*
 * Roll back a failed L2 drain so the target granule remains delegated and the
 * IPA remains unassigned.
 */
TEST(rtt_data_map_tests, l2_drain_failure_rolls_back_partial_granules)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base;

	CHECK_TRUE(create_data_rtt_ctx_l2_only(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_L2_BLOCK_TOP));

	data_base = reserve_delegated_granules_l2_aligned(1U);

	smc_rtt_data_map_complete(ctx.rd, TEST_DATA_IPA_BASE,
				  TEST_DATA_L2_BLOCK_TOP,
				  make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
				  make_data_map_desc(1UL, data_base,
						     RMI_BLOCK_L2),
				  &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(data_base);
	expect_ipa_unassigned_no_drain(&ctx, TEST_DATA_IPA_BASE);
}

/* ------------------------------------------------------------------ *
 * SRO yield and resume                                               *
 * ------------------------------------------------------------------ */

#ifdef RMM_RTT_MAP_UNMAP_CHECK_ISR_EL1
/*
 * Yield during the DATA_MAP drain path and complete the pending operation
 * through RMI_OP_CONTINUE.
 */
TEST(rtt_data_map_tests, l3_data_map_yields_during_drain_then_continues)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_pa;
	unsigned long desc;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_PAGE_TOP));
	data_pa = reserve_delegated_granules(1U);
	desc = make_data_map_desc(1UL, data_pa);

	prime_isr_yield_during_data_map_drain();

	smc_rtt_data_map(ctx.rd, TEST_DATA_IPA_BASE, TEST_DATA_PAGE_TOP,
			 make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
			 desc, &res);

	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	expect_data_granule_delegated(data_pa);
	CHECK_TRUE(s2tte_drain_pending(
		read_data_ipa_raw_s2tte(&ctx, TEST_DATA_IPA_BASE)));

	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_PAGE_TOP, res.x[1]);
	expect_data_granule_data_state(data_pa);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE, data_pa);
}

/*
 * Yield again from RMI_OP_CONTINUE while the DATA_MAP drain marker is still
 * present, then complete using the original handle.
 */
TEST(rtt_data_map_tests, data_map_continue_yields_again_during_drain)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	return_code_t rc;
	uintptr_t data_pa;
	unsigned long desc;
	unsigned long handle;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_PAGE_TOP));
	data_pa = reserve_delegated_granules(1U);
	desc = make_data_map_desc(1UL, data_pa);

	prime_isr_yield_during_data_map_drain();

	smc_rtt_data_map(ctx.rd, TEST_DATA_IPA_BASE, TEST_DATA_PAGE_TOP,
			 make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
			 desc, &res);

	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	handle = res.x[1];
	expect_data_granule_delegated(data_pa);
	CHECK_TRUE(s2tte_drain_pending(
		read_data_ipa_raw_s2tte(&ctx, TEST_DATA_IPA_BASE)));

	prime_isr_pending_irq();
	smc_op_continue(handle, 0UL, &res);

	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));
	CHECK_EQUAL(RMI_OP_CANNOT_CANCEL,
		    (unsigned long)EXTRACT(RMI_OP_CAN_CANCEL_BIT, res.x[0]));
	CHECK_EQUAL(0UL, res.x[1]);
	expect_data_granule_delegated(data_pa);
	CHECK_TRUE(s2tte_drain_pending(
		read_data_ipa_raw_s2tte(&ctx, TEST_DATA_IPA_BASE)));

	prime_isr_no_pending_irq();
	smc_op_continue(handle, 0UL, &res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(TEST_DATA_PAGE_TOP, res.x[1]);
	expect_data_granule_data_state(data_pa);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE, data_pa);
}

/*
 * Yield during rollback after an L2 DATA_MAP drain fails, then complete the
 * rollback through RMI_OP_CONTINUE. The test delegates only the first backing
 * granule of the L2 block, so draining the second granule fails with
 * RMI_ERROR_INPUT when it is not found in DELEGATED state.
 */
TEST(rtt_data_map_tests, l2_data_map_yields_during_rollback_then_continues)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	uintptr_t data_base;

	CHECK_TRUE(create_data_rtt_ctx_l2_only(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_L2_BLOCK_TOP));

	data_base = reserve_delegated_granules_l2_aligned(1U);
	prime_isr_yield_during_data_map_rollback();

	smc_rtt_data_map(ctx.rd, TEST_DATA_IPA_BASE,
			 TEST_DATA_L2_BLOCK_TOP,
			 make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
			 make_data_map_desc(1UL, data_base, RMI_BLOCK_L2),
			 &res);

	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	expect_data_granule_data_state(data_base);
	CHECK_TRUE(s2tte_drain_pending(
		read_data_ipa_raw_s2tte(&ctx, TEST_DATA_IPA_BASE)));

	res = sro_complete_operation(res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_data_granule_delegated(data_base);
	expect_ipa_unassigned_no_drain(&ctx, TEST_DATA_IPA_BASE);
}

/*
 * Reject a retry while the IPA carries the drain-pending marker, then complete
 * the original operation.
 */
TEST(rtt_data_map_tests, drain_pending_map_retry_returns_busy)
{
	struct test_data_ctx ctx;
	struct smc_result res = {};
	struct smc_result retry_res = {};
	uintptr_t data_pa;
	uintptr_t retry_pa;

	CHECK_TRUE(create_data_rtt_ctx(&ctx));
	CHECK_TRUE(init_ripas_range(&ctx, TEST_DATA_IPA_BASE,
				    TEST_DATA_PAGE_TOP));

	data_pa = reserve_delegated_granules(1U);
	prime_isr_yield_during_data_map_drain();
	smc_rtt_data_map(ctx.rd, TEST_DATA_IPA_BASE, TEST_DATA_PAGE_TOP,
			 make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
			 make_data_map_desc(1UL, data_pa), &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);

	retry_pa = reserve_delegated_granules(1U);
	smc_rtt_data_map(ctx.rd, TEST_DATA_IPA_BASE, TEST_DATA_PAGE_TOP,
			 make_data_map_flags(RMI_ADDR_TYPE_SINGLE),
			 make_data_map_desc(1UL, retry_pa), &retry_res);

	CHECK_EQUAL(RMI_BUSY, retry_res.x[0]);
	expect_data_granule_delegated(retry_pa);
	CHECK_TRUE(s2tte_drain_pending(
		read_data_ipa_raw_s2tte(&ctx, TEST_DATA_IPA_BASE)));

	res = sro_complete_operation(res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	expect_data_granule_data_state(data_pa);
	expect_data_granule_delegated(retry_pa);
	expect_ipa_assigned_ram_to_pa(&ctx, TEST_DATA_IPA_BASE, data_pa);
}
#endif

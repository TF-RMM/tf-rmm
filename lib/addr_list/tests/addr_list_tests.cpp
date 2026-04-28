/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <addr_list.h>
#include <arch_helpers.h>
#include <debug.h>
#include <granule.h>
#include <host_utils.h>
#include <smc-rmi.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
#include <xlat_defs.h>
}

/*
 * Helper to get a granule physical address by index.
 */
static uintptr_t granule_addr(unsigned int idx)
{
	return host_util_get_granule_base() + (uintptr_t)idx * GRANULE_SIZE;
}

/*
 * Helper: return a random state (DELEGATE or UNDELEGATE).
 */
static unsigned long rand_state(void)
{
	return test_helpers_get_rand_in_range(
			RMI_OP_MEM_DELEGATED, RMI_OP_MEM_UNDELEGATED);
}

/*
 * Helper: return a random RTT level suitable for addr_list_add_block.
 * The sz encoding in the descriptor is (XLAT_TABLE_LEVEL_MAX - level).
 * The SZ field is 2 bits wide, so valid levels are LEVEL_MAX down to
 * LEVEL_MAX - 3 (i.e. levels 3, 2, 1, 0 when LEVEL_MAX == 3).
 */
static unsigned long rand_level(void)
{
	unsigned long max_sz = (1UL << RMI_ADDR_RDESC_4K_SZ_WIDTH) - 1UL;

	return (unsigned long)XLAT_TABLE_LEVEL_MAX -
		test_helpers_get_rand_in_range(0UL, max_sz);
}

/*
 * Helper: return a granule address properly aligned for the given RTT level.
 * Uses a random granule index as starting point.
 */
static uintptr_t rand_aligned_addr(unsigned long rtt_level)
{
	unsigned long rand_idx = test_helpers_get_rand_in_range(10UL, 200UL);
	uintptr_t raw = granule_addr((unsigned int)rand_idx);
	unsigned long blk_size = XLAT_BLOCK_SIZE(rtt_level);

	return round_up(raw, blk_size);
}

/*
 * Helper: compute the descriptor sz encoding from an RTT level.
 */
static unsigned long level_to_sz(unsigned long rtt_level)
{
	return (unsigned long)XLAT_TABLE_LEVEL_MAX - rtt_level;
}

/*
 * Helper: verify that all range_desc entries in [from, ADDR_LIST_MAX_RANGES)
 * are zero.
 */
static void check_descs_zero(struct addr_list *list, unsigned long from)
{
	for (unsigned long i = from; i < ADDR_LIST_MAX_RANGES; i++) {
		UNSIGNED_LONGS_EQUAL_TEXT(0UL, list->range_desc[i],
			"Expected zero descriptor");
	}
}

/*
 * Helper: verify descriptor fields match expected values.
 */
static void check_desc(struct addr_list *list, unsigned long idx,
		       unsigned long expected_addr, unsigned long expected_cnt,
		       unsigned long expected_sz, unsigned long expected_st)
{
	unsigned long desc = list->range_desc[idx];

	UNSIGNED_LONGS_EQUAL(expected_addr,
		EXTRACT(RMI_ADDR_RDESC_4K_ADDR, desc) << GRANULE_SHIFT);
	UNSIGNED_LONGS_EQUAL(expected_cnt,
		EXTRACT(RMI_ADDR_RDESC_4K_CNT, desc));
	UNSIGNED_LONGS_EQUAL(expected_sz,
		EXTRACT(RMI_ADDR_RDESC_4K_SZ, desc));
	UNSIGNED_LONGS_EQUAL(expected_st,
		EXTRACT(RMI_ADDR_RDESC_4K_ST, desc));
}

/* ================================================================
 * Test Group for direct addr_list API unit tests.
 * ================================================================
 */

TEST_GROUP(addr_list_tests) {
	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start(false);
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
	}
	TEST_TEARDOWN()
	{
	}
};

/* ================================================================
 * addr_list_init() tests
 * ================================================================
 */

/* ----------------------------------------------------------------
 * TC_INIT_01: Init with LIST_TYPE_INPUT sets type and empties list.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, init_input_list)
{
	struct addr_list list;

	/* Poison the struct first so we can verify init clears it */
	(void)memset(&list, 0xFF, sizeof(list));

	addr_list_init(&list, LIST_TYPE_INPUT);

	CHECK_TRUE(addr_list_is_empty(&list));
	UNSIGNED_LONGS_EQUAL(LIST_TYPE_INPUT, list.type);
	UNSIGNED_LONGS_EQUAL(0UL, list.count);
	check_descs_zero(&list, 0);
}

/* ----------------------------------------------------------------
 * TC_INIT_02: Init with LIST_TYPE_OUTPUT sets type and empties list.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, init_output_list)
{
	struct addr_list list;

	(void)memset(&list, 0xFF, sizeof(list));

	addr_list_init(&list, LIST_TYPE_OUTPUT);

	CHECK_TRUE(addr_list_is_empty(&list));
	UNSIGNED_LONGS_EQUAL(LIST_TYPE_OUTPUT, list.type);
	UNSIGNED_LONGS_EQUAL(0UL, list.count);
	check_descs_zero(&list, 0);
}

/* ================================================================
 * addr_list_add_block() tests
 * ================================================================
 */

/* ----------------------------------------------------------------
 * TC_ADD_01: Add first block to empty list — verify descriptor
 *            content and unused entries are zero.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, add_block_first_entry)
{
	struct addr_list list;
	unsigned long rtt_level = rand_level();
	unsigned long st = rand_state();
	uintptr_t addr = rand_aligned_addr(rtt_level);

	addr_list_init(&list, LIST_TYPE_OUTPUT);

	bool ret = addr_list_add_block(&list, addr, rtt_level, st);

	CHECK_TRUE(ret);
	CHECK_FALSE(addr_list_is_empty(&list));
	UNSIGNED_LONGS_EQUAL(1UL, list.count);

	/* Verify descriptor 0 has the right content */
	check_desc(&list, 0, addr, 1UL, level_to_sz(rtt_level), st);

	/* All other descriptors must be zero */
	check_descs_zero(&list, 1);
}

/* ----------------------------------------------------------------
 * TC_ADD_02: Misaligned block_addr → returns false, list unchanged.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, add_block_misaligned_addr)
{
	struct addr_list list;
	unsigned long rtt_level = rand_level();
	unsigned long st = rand_state();
	unsigned long blk_size = XLAT_BLOCK_SIZE(rtt_level);
	unsigned long misalign = test_helpers_get_rand_in_range(1UL,
						blk_size - 1UL);
	uintptr_t addr = rand_aligned_addr(rtt_level) + misalign;

	addr_list_init(&list, LIST_TYPE_OUTPUT);

	bool ret = addr_list_add_block(&list, addr, rtt_level, st);

	CHECK_FALSE(ret);
	CHECK_TRUE(addr_list_is_empty(&list));
	UNSIGNED_LONGS_EQUAL(0UL, list.count);
	check_descs_zero(&list, 0);
}

/* ----------------------------------------------------------------
 * TC_ADD_03: Append contiguous block — merges into single descriptor
 *            with count=2.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, add_block_append_to_range)
{
	struct addr_list list;
	unsigned long rtt_level = rand_level();
	unsigned long st = rand_state();
	unsigned long blk_size = XLAT_BLOCK_SIZE(rtt_level);
	uintptr_t addr0 = rand_aligned_addr(rtt_level);
	uintptr_t addr1 = addr0 + blk_size; /* contiguous, after addr0 */

	addr_list_init(&list, LIST_TYPE_OUTPUT);

	CHECK_TRUE(addr_list_add_block(&list, addr0, rtt_level, st));
	CHECK_TRUE(addr_list_add_block(&list, addr1, rtt_level, st));

	/* Merged into one descriptor with count=2 */
	UNSIGNED_LONGS_EQUAL(1UL, list.count);
	check_desc(&list, 0, addr0, 2UL, level_to_sz(rtt_level), st);
	check_descs_zero(&list, 1);
}

/* ----------------------------------------------------------------
 * TC_ADD_04: Prepend contiguous block — merges into single descriptor.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, add_block_prepend_to_range)
{
	struct addr_list list;
	unsigned long rtt_level = rand_level();
	unsigned long st = rand_state();
	unsigned long blk_size = XLAT_BLOCK_SIZE(rtt_level);
	uintptr_t addr0 = rand_aligned_addr(rtt_level);
	uintptr_t addr1 = addr0 + blk_size;

	addr_list_init(&list, LIST_TYPE_OUTPUT);

	/* Add second (higher) address first, then prepend */
	CHECK_TRUE(addr_list_add_block(&list, addr1, rtt_level, st));
	CHECK_TRUE(addr_list_add_block(&list, addr0, rtt_level, st));

	/* Merged: base should be addr0, count=2 */
	UNSIGNED_LONGS_EQUAL(1UL, list.count);
	check_desc(&list, 0, addr0, 2UL, level_to_sz(rtt_level), st);
	check_descs_zero(&list, 1);
}

/* ----------------------------------------------------------------
 * TC_ADD_05: Non-contiguous addresses create separate descriptors.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, add_block_non_contiguous_creates_new_desc)
{
	struct addr_list list;
	unsigned long rtt_level = rand_level();
	unsigned long st = rand_state();
	unsigned long blk_size = XLAT_BLOCK_SIZE(rtt_level);
	uintptr_t addr0 = rand_aligned_addr(rtt_level);
	/* Ensure a gap of at least 2 blocks */
	uintptr_t addr1 = round_up(addr0 + blk_size * 10UL, blk_size);

	addr_list_init(&list, LIST_TYPE_OUTPUT);

	CHECK_TRUE(addr_list_add_block(&list, addr0, rtt_level, st));
	CHECK_TRUE(addr_list_add_block(&list, addr1, rtt_level, st));

	UNSIGNED_LONGS_EQUAL(2UL, list.count);
	check_desc(&list, 0, addr0, 1UL, level_to_sz(rtt_level), st);
	check_desc(&list, 1, addr1, 1UL, level_to_sz(rtt_level), st);
	check_descs_zero(&list, 2);
}

/* ----------------------------------------------------------------
 * TC_ADD_06: Different block size prevents merging.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, add_block_different_blk_size_no_merge)
{
	struct addr_list list;
	unsigned long st = rand_state();
	uintptr_t addr_l3 = granule_addr(60U);
	unsigned long l2_size = XLAT_BLOCK_SIZE(XLAT_TABLE_LEVEL_MAX - 1);
	uintptr_t addr_l2 = round_up(granule_addr(70U), l2_size);
	unsigned long l2_level = (unsigned long)XLAT_TABLE_LEVEL_MAX - 1UL;

	addr_list_init(&list, LIST_TYPE_OUTPUT);

	CHECK_TRUE(addr_list_add_block(&list, addr_l3,
			(unsigned long)XLAT_TABLE_LEVEL_MAX, st));
	CHECK_TRUE(addr_list_add_block(&list, addr_l2, l2_level, st));

	UNSIGNED_LONGS_EQUAL(2UL, list.count);
	check_desc(&list, 0, addr_l3, 1UL, RMI_PAGE_L3, st);
	/* L2 size encoding: level_max - level = 3 - 2 = 1 */
	check_desc(&list, 1, addr_l2, 1UL, 1UL, st);
	check_descs_zero(&list, 2);
}

/* ----------------------------------------------------------------
 * TC_ADD_07: Different state prevents merging.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, add_block_different_state_no_merge)
{
	struct addr_list list;
	unsigned long rtt_level = rand_level();
	unsigned long blk_size = XLAT_BLOCK_SIZE(rtt_level);
	uintptr_t addr0 = rand_aligned_addr(rtt_level);
	uintptr_t addr1 = addr0 + blk_size; /* contiguous */

	addr_list_init(&list, LIST_TYPE_OUTPUT);

	CHECK_TRUE(addr_list_add_block(&list, addr0, rtt_level,
			RMI_OP_MEM_DELEGATED));
	CHECK_TRUE(addr_list_add_block(&list, addr1, rtt_level,
			RMI_OP_MEM_UNDELEGATED));

	UNSIGNED_LONGS_EQUAL(2UL, list.count);
	check_desc(&list, 0, addr0, 1UL, level_to_sz(rtt_level),
		   RMI_OP_MEM_DELEGATED);
	check_desc(&list, 1, addr1, 1UL, level_to_sz(rtt_level),
		   RMI_OP_MEM_UNDELEGATED);
	check_descs_zero(&list, 2);
}

/* ----------------------------------------------------------------
 * TC_ADD_08: Descriptor count overflow creates a new descriptor.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, add_block_max_count_overflow_creates_new_desc)
{
	struct addr_list list;
	unsigned long max_cnt = (1UL << RMI_ADDR_RDESC_4K_CNT_WIDTH) - 1UL;
	unsigned long st = rand_state();
	uintptr_t base = granule_addr(100U);

	addr_list_init(&list, LIST_TYPE_OUTPUT);

	for (unsigned long i = 0; i < max_cnt; i++) {
		CHECK_TRUE(addr_list_add_block(&list,
				base + i * GRANULE_SIZE,
				(unsigned long)XLAT_TABLE_LEVEL_MAX, st));
	}
	UNSIGNED_LONGS_EQUAL(1UL, list.count);
	check_desc(&list, 0, base, max_cnt, RMI_PAGE_L3, st);

	/* Next block overflows the count → new descriptor */
	uintptr_t overflow_addr = base + max_cnt * GRANULE_SIZE;
	CHECK_TRUE(addr_list_add_block(&list, overflow_addr,
			(unsigned long)XLAT_TABLE_LEVEL_MAX, st));

	UNSIGNED_LONGS_EQUAL(2UL, list.count);
	check_desc(&list, 0, base, max_cnt, RMI_PAGE_L3, st);
	check_desc(&list, 1, overflow_addr, 1UL, RMI_PAGE_L3, st);
	check_descs_zero(&list, 2);
}

/* ----------------------------------------------------------------
 * TC_ADD_09: Fill list to ADDR_LIST_MAX_RANGES, then next add fails.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, add_block_list_full)
{
	struct addr_list list;
	unsigned long st = rand_state();
	uintptr_t base = granule_addr(100U);

	addr_list_init(&list, LIST_TYPE_OUTPUT);

	/* Add non-contiguous blocks to fill all descriptors */
	for (unsigned long i = 0; i < ADDR_LIST_MAX_RANGES; i++) {
		uintptr_t addr = base + i * 2UL * GRANULE_SIZE;
		CHECK_TRUE(addr_list_add_block(&list, addr,
				(unsigned long)XLAT_TABLE_LEVEL_MAX, st));
	}
	UNSIGNED_LONGS_EQUAL(ADDR_LIST_MAX_RANGES, list.count);

	/* Verify each descriptor has count=1 and the right address */
	for (unsigned long i = 0; i < ADDR_LIST_MAX_RANGES; i++) {
		uintptr_t expected = base + i * 2UL * GRANULE_SIZE;
		check_desc(&list, i, expected, 1UL, RMI_PAGE_L3, st);
	}

	/* One more fails */
	uintptr_t overflow_addr = base + ADDR_LIST_MAX_RANGES * 2UL * GRANULE_SIZE;
	CHECK_FALSE(addr_list_add_block(&list, overflow_addr,
			(unsigned long)XLAT_TABLE_LEVEL_MAX, st));

	/* List unchanged */
	UNSIGNED_LONGS_EQUAL(ADDR_LIST_MAX_RANGES, list.count);
}

/* ----------------------------------------------------------------
 * TC_ADD_10: Merge with second descriptor after gap from first.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, add_block_merge_with_second_descriptor)
{
	struct addr_list list;
	unsigned long rtt_level = rand_level();
	unsigned long st = rand_state();
	unsigned long blk_size = XLAT_BLOCK_SIZE(rtt_level);
	uintptr_t addr0 = rand_aligned_addr(rtt_level);
	/* Ensure a gap so two separate descriptors are created */
	uintptr_t addr1 = round_up(addr0 + blk_size * 10UL, blk_size);

	addr_list_init(&list, LIST_TYPE_OUTPUT);

	CHECK_TRUE(addr_list_add_block(&list, addr0, rtt_level, st));
	CHECK_TRUE(addr_list_add_block(&list, addr1, rtt_level, st));
	UNSIGNED_LONGS_EQUAL(2UL, list.count);

	/* Append to second descriptor */
	uintptr_t addr2 = addr1 + blk_size;
	CHECK_TRUE(addr_list_add_block(&list, addr2, rtt_level, st));

	/* Still 2 descriptors; second has count=2 */
	UNSIGNED_LONGS_EQUAL(2UL, list.count);
	check_desc(&list, 0, addr0, 1UL, level_to_sz(rtt_level), st);
	check_desc(&list, 1, addr1, 2UL, level_to_sz(rtt_level), st);
	check_descs_zero(&list, 2);
}

/* ================================================================
 * addr_list_reduce_first_block() tests
 *
 * These tests use build_input_list() to create INPUT lists via raw
 * descriptor encoding, since addr_list_add_block() asserts on
 * non-OUTPUT lists.
 * ================================================================
 */

/*
 * Helper to append one descriptor to an INPUT list via raw encoding.
 * Each call adds a new descriptor entry at list->count and increments it.
 */
static void build_input_list(struct addr_list *list,
			     uintptr_t base, unsigned long count,
			     unsigned long rtt_level, unsigned long st)
{
	unsigned long idx = list->count;

	assert(idx < ADDR_LIST_MAX_RANGES);

	list->range_desc[idx] =
		INPLACE(RMI_ADDR_RDESC_4K_SZ, level_to_sz(rtt_level)) |
		INPLACE(RMI_ADDR_RDESC_4K_CNT, count) |
		INPLACE(RMI_ADDR_RDESC_4K_ADDR, base >> GRANULE_SHIFT) |
		INPLACE(RMI_ADDR_RDESC_4K_ST, st);
	list->count = idx + 1UL;
}

/* ----------------------------------------------------------------
 * TC_REDUCE_01: Reduce on empty list returns false, list unchanged.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, reduce_empty_list)
{
	struct addr_list list;
	unsigned long addr, st;
	int level;

	addr_list_init(&list, LIST_TYPE_INPUT);

	bool ret = addr_list_reduce_first_block(&list, &addr, &level, &st);
	CHECK_FALSE(ret);
	CHECK_TRUE(addr_list_is_empty(&list));
	check_descs_zero(&list, 0);
}

/* ----------------------------------------------------------------
 * TC_REDUCE_02: Single block — reduce returns it with correct
 *               addr/level/state, descriptor count becomes 0.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, reduce_single_block)
{
	struct addr_list list;
	unsigned long rtt_level = rand_level();
	unsigned long st = rand_state();
	uintptr_t base = rand_aligned_addr(rtt_level);
	unsigned long addr, out_st;
	int level;

	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base, 1UL, rtt_level, st);

	bool ret = addr_list_reduce_first_block(&list, &addr, &level, &out_st);
	CHECK_TRUE(ret);
	UNSIGNED_LONGS_EQUAL(base, addr);
	UNSIGNED_LONGS_EQUAL(rtt_level, level);
	UNSIGNED_LONGS_EQUAL(st, out_st);

	/* Descriptor 0 count should now be 0 */
	UNSIGNED_LONGS_EQUAL(0UL,
		EXTRACT(RMI_ADDR_RDESC_4K_CNT, list.range_desc[0]));

	/* Remaining descriptors untouched */
	check_descs_zero(&list, 1);

	/* Next call returns false */
	ret = addr_list_reduce_first_block(&list, &addr, &level, &out_st);
	CHECK_FALSE(ret);
}

/* ----------------------------------------------------------------
 * TC_REDUCE_03: Descriptor with count=3 — reduce three times,
 *               each returns correct advancing address. Verify
 *               count decrements and addr advances in descriptor.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, reduce_multiple_blocks)
{
	struct addr_list list;
	unsigned long rtt_level = rand_level();
	unsigned long st = rand_state();
	unsigned long blk_size = XLAT_BLOCK_SIZE(rtt_level);
	uintptr_t base = rand_aligned_addr(rtt_level);
	unsigned long addr, out_st;
	int level;
	unsigned long num_blocks = (unsigned long)test_helpers_get_rand_in_range(
					2UL, 5UL);

	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base, num_blocks, rtt_level, st);

	for (unsigned long i = 0; i < num_blocks; i++) {
		bool ret = addr_list_reduce_first_block(&list,
				&addr, &level, &out_st);
		CHECK_TRUE(ret);
		UNSIGNED_LONGS_EQUAL(base + i * blk_size, addr);
		UNSIGNED_LONGS_EQUAL(rtt_level, level);
		UNSIGNED_LONGS_EQUAL(st, out_st);

		/* Verify count in descriptor decremented */
		UNSIGNED_LONGS_EQUAL(num_blocks - i - 1UL,
			EXTRACT(RMI_ADDR_RDESC_4K_CNT, list.range_desc[0]));
	}

	/* All exhausted */
	CHECK_FALSE(addr_list_reduce_first_block(&list, &addr, &level, &out_st));
	check_descs_zero(&list, 1);
}

/* ----------------------------------------------------------------
 * TC_REDUCE_04: Skip empty descriptors — first desc has cnt=0,
 *               second has cnt=1. Reduce returns block from second.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, reduce_skip_empty_descriptors)
{
	struct addr_list list;
	unsigned long rtt_level = rand_level();
	unsigned long st = rand_state();
	unsigned long blk_size = XLAT_BLOCK_SIZE(rtt_level);
	uintptr_t base0 = rand_aligned_addr(rtt_level);
	uintptr_t base1 = round_up(base0 + blk_size * 10UL, blk_size);
	unsigned long addr, out_st;
	int level;

	addr_list_init(&list, LIST_TYPE_INPUT);

	/* Create two non-contiguous descriptors */
	build_input_list(&list, base0, 1UL, rtt_level, st);
	build_input_list(&list, base1, 1UL, rtt_level, st);
	UNSIGNED_LONGS_EQUAL(2UL, list.count);

	/* Exhaust first descriptor */
	CHECK_TRUE(addr_list_reduce_first_block(&list, &addr, &level, &out_st));
	UNSIGNED_LONGS_EQUAL(base0, addr);

	/* Now desc[0] is empty. Next reduce should skip it and
	 * return from desc[1] */
	CHECK_TRUE(addr_list_reduce_first_block(&list, &addr, &level, &out_st));
	UNSIGNED_LONGS_EQUAL(base1, addr);
	UNSIGNED_LONGS_EQUAL(rtt_level, level);
	UNSIGNED_LONGS_EQUAL(st, out_st);

	/* No more */
	CHECK_FALSE(addr_list_reduce_first_block(&list, &addr, &level, &out_st));
}

/* ----------------------------------------------------------------
 * TC_REDUCE_05: All descriptors empty (cnt=0) → returns false.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, reduce_all_descriptors_empty)
{
	struct addr_list list;
	unsigned long st = rand_state();
	unsigned long rtt_level = rand_level();
	unsigned long blk_size = XLAT_BLOCK_SIZE(rtt_level);
	uintptr_t base0 = rand_aligned_addr(rtt_level);
	uintptr_t base1 = round_up(base0 + blk_size * 10UL, blk_size);

	addr_list_init(&list, LIST_TYPE_INPUT);

	/* Create two non-contiguous descriptors */
	build_input_list(&list, base0, 1UL, rtt_level, st);
	build_input_list(&list, base1, 1UL, rtt_level, st);
	UNSIGNED_LONGS_EQUAL(2UL, list.count);

	/* Exhaust both descriptors */
	unsigned long addr, out_st;
	int level;
	CHECK_TRUE(addr_list_reduce_first_block(&list, &addr, &level, &out_st));
	CHECK_TRUE(addr_list_reduce_first_block(&list, &addr, &level, &out_st));

	/* Both exhausted — next call returns false */
	CHECK_FALSE(addr_list_reduce_first_block(&list, &addr, &level, &out_st));

	/* Both descriptor counts should be 0 */
	UNSIGNED_LONGS_EQUAL(0UL,
		EXTRACT(RMI_ADDR_RDESC_4K_CNT, list.range_desc[0]));
	UNSIGNED_LONGS_EQUAL(0UL,
		EXTRACT(RMI_ADDR_RDESC_4K_CNT, list.range_desc[1]));
	check_descs_zero(&list, 2);
}

/* ----------------------------------------------------------------
 * TC_REDUCE_06: Reduce with randomized address and UNDELEGATE state.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, reduce_undelegate_state)
{
	struct addr_list list;
	unsigned long rtt_level = rand_level();
	uintptr_t base = rand_aligned_addr(rtt_level);
	unsigned long addr, out_st;
	int level;

	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base, 1UL, rtt_level,
			      RMI_OP_MEM_UNDELEGATED);

	bool ret = addr_list_reduce_first_block(&list, &addr, &level, &out_st);
	CHECK_TRUE(ret);
	UNSIGNED_LONGS_EQUAL(base, addr);
	UNSIGNED_LONGS_EQUAL(rtt_level, level);
	UNSIGNED_LONGS_EQUAL(RMI_OP_MEM_UNDELEGATED, out_st);

	/* Descriptor should now be exhausted */
	UNSIGNED_LONGS_EQUAL(0UL,
		EXTRACT(RMI_ADDR_RDESC_4K_CNT, list.range_desc[0]));
	check_descs_zero(&list, 1);

	CHECK_FALSE(addr_list_reduce_first_block(&list, &addr, &level, &out_st));
}

/* ----------------------------------------------------------------
 * TC_REDUCE_07: Two descriptors — exhaust first then second.
 *               Verify addresses, levels, states, and descriptor
 *               content after each step.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, reduce_across_two_descriptors)
{
	struct addr_list list;
	unsigned long rtt_level = rand_level();
	unsigned long st = rand_state();
	unsigned long blk_size = XLAT_BLOCK_SIZE(rtt_level);
	uintptr_t base0 = rand_aligned_addr(rtt_level);
	uintptr_t base1 = round_up(base0 + blk_size * 10UL, blk_size);
	unsigned long addr, out_st;
	int level;

	addr_list_init(&list, LIST_TYPE_INPUT);

	/* First descriptor: 2 contiguous blocks */
	build_input_list(&list, base0, 2UL, rtt_level, st);
	/* Second descriptor: 1 block (gap forces new descriptor) */
	build_input_list(&list, base1, 1UL, rtt_level, st);
	UNSIGNED_LONGS_EQUAL(2UL, list.count);

	/* First block from descriptor 0 */
	CHECK_TRUE(addr_list_reduce_first_block(&list, &addr, &level, &out_st));
	UNSIGNED_LONGS_EQUAL(base0, addr);
	UNSIGNED_LONGS_EQUAL(rtt_level, level);
	UNSIGNED_LONGS_EQUAL(st, out_st);
	/* desc[0] count decremented to 1 */
	UNSIGNED_LONGS_EQUAL(1UL,
		EXTRACT(RMI_ADDR_RDESC_4K_CNT, list.range_desc[0]));
	/* desc[1] untouched */
	UNSIGNED_LONGS_EQUAL(1UL,
		EXTRACT(RMI_ADDR_RDESC_4K_CNT, list.range_desc[1]));

	/* Second block from descriptor 0 */
	CHECK_TRUE(addr_list_reduce_first_block(&list, &addr, &level, &out_st));
	UNSIGNED_LONGS_EQUAL(base0 + blk_size, addr);
	/* desc[0] now exhausted */
	UNSIGNED_LONGS_EQUAL(0UL,
		EXTRACT(RMI_ADDR_RDESC_4K_CNT, list.range_desc[0]));

	/* Third block from descriptor 1 */
	CHECK_TRUE(addr_list_reduce_first_block(&list, &addr, &level, &out_st));
	UNSIGNED_LONGS_EQUAL(base1, addr);
	UNSIGNED_LONGS_EQUAL(st, out_st);
	/* desc[1] now exhausted */
	UNSIGNED_LONGS_EQUAL(0UL,
		EXTRACT(RMI_ADDR_RDESC_4K_CNT, list.range_desc[1]));

	/* No more */
	CHECK_FALSE(addr_list_reduce_first_block(&list, &addr, &level, &out_st));
	check_descs_zero(&list, 2);
}

/* ================================================================
 * addr_list_validate() tests
 * ================================================================
 */

/* ----------------------------------------------------------------
 * TC_VALIDATE_01: Valid single-entry list → true, total_mem correct.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, validate_single_valid_entry)
{
	struct addr_list list;
	unsigned long rand_cnt = (unsigned long)test_helpers_get_rand_in_range(
					1UL, 10UL);
	unsigned long st = rand_state();
	uintptr_t base = granule_addr(500U);

	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base, rand_cnt,
			      (unsigned long)XLAT_TABLE_LEVEL_MAX, st);

	unsigned long total_mem = 0UL;
	bool ret = addr_list_validate(&list, false, &total_mem, st);
	CHECK_TRUE(ret);
	UNSIGNED_LONGS_EQUAL(rand_cnt * GRANULE_SIZE, total_mem);
}

/* ----------------------------------------------------------------
 * TC_VALIDATE_02: Empty list (count == 0) → valid.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, validate_zero_count)
{
	struct addr_list list;
	unsigned long st = rand_state();

	addr_list_init(&list, LIST_TYPE_INPUT);

	unsigned long total_mem = 0UL;
	bool ret = addr_list_validate(&list, false, &total_mem, st);
	CHECK_TRUE(ret);
	UNSIGNED_LONGS_EQUAL(0UL, total_mem);
}

/* ----------------------------------------------------------------
 * TC_VALIDATE_03: count > ADDR_LIST_MAX_RANGES → assert.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, validate_count_exceeds_max)
{
	struct addr_list list;

	addr_list_init(&list, LIST_TYPE_INPUT);
	list.count = ADDR_LIST_MAX_RANGES + 1UL;

	unsigned long total_mem = 0UL;

	test_helpers_expect_assert_fail(true);
	(void)addr_list_validate(&list, false,
			&total_mem, RMI_OP_MEM_DELEGATED);
	test_helpers_expect_assert_fail(false);
}

/* ----------------------------------------------------------------
 * TC_VALIDATE_04: Unaligned base address for L2 block → false.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, validate_unaligned_base_addr)
{
	struct addr_list list;
	unsigned long st = rand_state();
	unsigned long l2_level = (unsigned long)XLAT_TABLE_LEVEL_MAX - 1UL;
	unsigned long l2_size = XLAT_BLOCK_SIZE(l2_level);
	uintptr_t base = granule_addr(510U);

	/* Ensure base is NOT aligned to L2 */
	uintptr_t aligned = round_up(base, l2_size);
	base = aligned + GRANULE_SIZE;

	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base, 1UL, l2_level, st);

	unsigned long total_mem = 0UL;
	bool ret = addr_list_validate(&list, false, &total_mem, st);
	CHECK_FALSE(ret);
}

/* ----------------------------------------------------------------
 * TC_VALIDATE_05: Wrong state in descriptor → false.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, validate_wrong_state)
{
	struct addr_list list;
	uintptr_t base = rand_aligned_addr((unsigned long)XLAT_TABLE_LEVEL_MAX);

	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base, 1UL,
			      (unsigned long)XLAT_TABLE_LEVEL_MAX,
			      RMI_OP_MEM_UNDELEGATED);

	unsigned long total_mem = 0UL;
	bool ret = addr_list_validate(&list, false,
			&total_mem, RMI_OP_MEM_DELEGATED);
	CHECK_FALSE(ret);
}

/* ----------------------------------------------------------------
 * TC_VALIDATE_06: Validate returns total memory correctly for
 *                 randomized count.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, validate_total_mem_calculation)
{
	struct addr_list list;
	unsigned long st = rand_state();
	uintptr_t base = rand_aligned_addr((unsigned long)XLAT_TABLE_LEVEL_MAX);
	unsigned long rand_cnt = (unsigned long)test_helpers_get_rand_in_range(
					2UL, 20UL);

	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base, rand_cnt,
			      (unsigned long)XLAT_TABLE_LEVEL_MAX, st);

	unsigned long total_mem = 0UL;
	bool ret = addr_list_validate(&list, false, &total_mem, st);
	CHECK_TRUE(ret);
	UNSIGNED_LONGS_EQUAL(rand_cnt * GRANULE_SIZE, total_mem);
}

/* ----------------------------------------------------------------
 * TC_VALIDATE_07: is_contig with two valid descriptors → false.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, validate_contig_two_valid_entries)
{
	struct addr_list list;
	unsigned long st = rand_state();
	uintptr_t base0 = granule_addr(540U);
	uintptr_t base1 = granule_addr(550U);

	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base0, 1UL,
			      (unsigned long)XLAT_TABLE_LEVEL_MAX, st);
	build_input_list(&list, base1, 1UL,
			      (unsigned long)XLAT_TABLE_LEVEL_MAX, st);

	unsigned long total_mem = 0UL;
	bool ret = addr_list_validate(&list, true, &total_mem, st);
	CHECK_FALSE(ret);
}

/* ----------------------------------------------------------------
 * TC_VALIDATE_08: is_contig with non-power-of-2 total → false.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, validate_contig_non_power_of_two)
{
	struct addr_list list;
	unsigned long st = rand_state();
	uintptr_t base = granule_addr(560U);

	/* 3 × 4KB = 12KB, not a power of 2 */
	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base, 3UL,
			      (unsigned long)XLAT_TABLE_LEVEL_MAX, st);

	unsigned long total_mem = 0UL;
	bool ret = addr_list_validate(&list, true, &total_mem, st);
	CHECK_FALSE(ret);
}

/* ----------------------------------------------------------------
 * TC_VALIDATE_09: is_contig — addr not aligned to total size → false.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, validate_contig_addr_not_aligned_to_total)
{
	struct addr_list list;
	unsigned long st = rand_state();
	unsigned long cnt = 2UL;
	unsigned long total = cnt * GRANULE_SIZE; /* 8 KB */

	/* Pick address aligned to 4KB but NOT to 8KB */
	uintptr_t pool = granule_addr(570U);
	uintptr_t aligned = round_up(pool, total);
	uintptr_t base = aligned + GRANULE_SIZE;

	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base, cnt,
			      (unsigned long)XLAT_TABLE_LEVEL_MAX, st);

	unsigned long total_mem = 0UL;
	bool ret = addr_list_validate(&list, true, &total_mem, st);
	CHECK_FALSE(ret);
}

/* ----------------------------------------------------------------
 * TC_VALIDATE_10: is_contig happy path — power-of-2, aligned → true.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, validate_contig_happy_path)
{
	struct addr_list list;
	unsigned long st = rand_state();
	unsigned long cnt = 2UL;
	unsigned long total = cnt * GRANULE_SIZE; /* 8 KB */

	uintptr_t pool = granule_addr(580U);
	uintptr_t base = round_up(pool, total);

	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base, cnt,
			      (unsigned long)XLAT_TABLE_LEVEL_MAX, st);

	unsigned long total_mem = 0UL;
	bool ret = addr_list_validate(&list, true, &total_mem, st);
	CHECK_TRUE(ret);
	UNSIGNED_LONGS_EQUAL(total, total_mem);
}

/* ----------------------------------------------------------------
 * TC_VALIDATE_11: Zero-count entries are skipped during validation.
 *
 * Build two non-contiguous descriptors, then reduce the first to
 * create a cnt=0 entry. Validate should skip it.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, validate_skips_zero_count_entries)
{
	struct addr_list list;
	unsigned long st = rand_state();
	uintptr_t base0 = granule_addr(590U);
	uintptr_t base1 = granule_addr(600U);

	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base0, 1UL,
			      (unsigned long)XLAT_TABLE_LEVEL_MAX, st);
	build_input_list(&list, base1, 1UL,
			      (unsigned long)XLAT_TABLE_LEVEL_MAX, st);
	UNSIGNED_LONGS_EQUAL(2UL, list.count);

	/* Exhaust first descriptor to make it cnt=0 */
	unsigned long addr, out_st;
	int level;
	CHECK_TRUE(addr_list_reduce_first_block(&list, &addr, &level, &out_st));
	UNSIGNED_LONGS_EQUAL(base0, addr);

	/* Now validate: only desc[1] contributes */
	unsigned long total_mem = 0UL;
	bool ret = addr_list_validate(&list, false, &total_mem, st);
	CHECK_TRUE(ret);
	UNSIGNED_LONGS_EQUAL(GRANULE_SIZE, total_mem);
}

/* ----------------------------------------------------------------
 * TC_VALIDATE_12: Total memory equals exact value → true.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, validate_total_equals_req_mem)
{
	struct addr_list list;
	unsigned long st = rand_state();
	uintptr_t base = granule_addr(610U);
	unsigned long rand_cnt = (unsigned long)test_helpers_get_rand_in_range(
					1UL, 15UL);

	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base, rand_cnt,
			      (unsigned long)XLAT_TABLE_LEVEL_MAX, st);

	unsigned long total_mem = 0UL;
	bool ret = addr_list_validate(&list, false, &total_mem, st);
	CHECK_TRUE(ret);
	UNSIGNED_LONGS_EQUAL(rand_cnt * GRANULE_SIZE, total_mem);
}

/* ----------------------------------------------------------------
 * TC_VALIDATE_13: Non-contiguous multi-descriptor list validates.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, validate_multi_desc_within_req_mem)
{
	struct addr_list list;
	unsigned long st = rand_state();
	uintptr_t base0 = granule_addr(620U);
	uintptr_t base1 = granule_addr(640U);

	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base0, 1UL,
			      (unsigned long)XLAT_TABLE_LEVEL_MAX, st);
	build_input_list(&list, base1, 1UL,
			      (unsigned long)XLAT_TABLE_LEVEL_MAX, st);

	unsigned long total_mem = 0UL;
	bool ret = addr_list_validate(&list, false, &total_mem, st);
	CHECK_TRUE(ret);
	UNSIGNED_LONGS_EQUAL(2UL * GRANULE_SIZE, total_mem);
}

/* ----------------------------------------------------------------
 * TC_VALIDATE_14: UNDELEGATE state match → passes.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, validate_undelegate_state_match)
{
	struct addr_list list;
	uintptr_t base = rand_aligned_addr((unsigned long)XLAT_TABLE_LEVEL_MAX);
	unsigned long rand_cnt = (unsigned long)test_helpers_get_rand_in_range(
					1UL, 10UL);

	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base, rand_cnt,
			      (unsigned long)XLAT_TABLE_LEVEL_MAX,
			      RMI_OP_MEM_UNDELEGATED);

	unsigned long total_mem = 0UL;
	bool ret = addr_list_validate(&list, false,
			&total_mem, RMI_OP_MEM_UNDELEGATED);
	CHECK_TRUE(ret);
	UNSIGNED_LONGS_EQUAL(rand_cnt * GRANULE_SIZE, total_mem);
}

/* ----------------------------------------------------------------
 * TC_VALIDATE_15: is_contig with only zero-count entries → true.
 *
 * Build a single block, reduce it to make cnt=0, then validate
 * with is_contig.
 * ----------------------------------------------------------------
 */
TEST(addr_list_tests, validate_contig_all_zero_count)
{
	struct addr_list list;
	unsigned long st = rand_state();
	uintptr_t base = rand_aligned_addr((unsigned long)XLAT_TABLE_LEVEL_MAX);

	addr_list_init(&list, LIST_TYPE_INPUT);
	build_input_list(&list, base, 1UL,
			      (unsigned long)XLAT_TABLE_LEVEL_MAX, st);

	/* Exhaust the only descriptor */
	unsigned long addr, out_st;
	int level;
	CHECK_TRUE(addr_list_reduce_first_block(&list, &addr, &level, &out_st));

	unsigned long total_mem = 0UL;
	bool ret = addr_list_validate(&list, true, &total_mem, st);
	CHECK_TRUE(ret);
	UNSIGNED_LONGS_EQUAL(0UL, total_mem);
}

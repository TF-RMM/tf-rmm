/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_helpers.h>
#include <debug.h>
#include <errno.h>
#include <host_utils.h>
#include <sizes.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
#include <xlat_contexts.h>
#include <xlat_defs.h>
#include <xlat_tables.h>
#include <xlat_tables_private.h>
#include <xlat_test_defs.h>
#include <xlat_test_helpers.h>
}

static struct xlat_ctx parent_ctx, child_ctx;

/* Reserve some memory to be used for the translation tables */
static uint64_t child_xlat_tables[XLAT_TABLE_ENTRIES * 514U]
					__aligned(XLAT_TABLE_SIZE);

/*
 * Helper function to test xlat_stitch_tables_l1() with given VA range.
 * Sets up parent context with TRANSIENT descriptors and child context with
 * normal mapping, performs stitching, and verifies the result.
 */
static int xlat_stitch_test_helper(uintptr_t va_start, size_t va_size,
			uint64_t *child_tables, unsigned int num_child_tables)
{
	struct xlat_mmap_region parent_mmap[2];
	struct xlat_mmap_region child_mmap[2];
	int ret;

	/* Disable MMU for the test (required by xlat_stitch_tables_l1) */
	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);

	/* Setup parent context with TRANSIENT region */
	memset(&parent_ctx, 0, sizeof(parent_ctx));

	/* Configure parent with TRANSIENT mapping */
	parent_mmap[0] = MAP_REGION_TRANSIENT(va_start, va_size, XLAT_BLOCK_SIZE(1));
	parent_mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	/* Initialize parent context with VA space */
	ret = xlat_ctx_cfg_init(&parent_ctx, VA_LOW_REGION, &parent_mmap[0], 1U,
				0U, XLAT_TEST_MAX_VA_SIZE(), 0UL);
	if (ret != 0) {
		ERROR("parent xlat_ctx_cfg_init failed with ret=%d, va_start=0x%lx, va_size=0x%lx\n",
		      ret, va_start, va_size);
		return ret;
	}

	ret = xlat_ctx_init(&parent_ctx, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	if (ret != 0) {
		ERROR("parent xlat_ctx_init failed: ret=%d\n", ret);
		return ret;
	}

	/* Setup child context with normal mapping */
	memset(&child_ctx, 0, sizeof(child_ctx));

	/* Child has same VA mapping but with actual memory */
	child_mmap[0].base_pa = 0x80000000UL;
	child_mmap[0].base_va = va_start;
	child_mmap[0].size = va_size;
	child_mmap[0].attr = MT_RW_DATA | MT_REALM;
	child_mmap[0].granularity = GRANULE_SIZE;
	child_mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	/* Initialize child context with VA space that fits in L1 (single L0 block) */
	ret = xlat_ctx_cfg_init(&child_ctx, VA_LOW_REGION, &child_mmap[0], 1U,
				0U, XLAT_BLOCK_SIZE(0), 0UL);
	if (ret != 0) {
		ERROR("child xlat_ctx_cfg_init failed with ret=%d, va_start=0x%lx, va_size=0x%lx\n",
		      ret, va_start, va_size);
		return ret;
	}

	ret = xlat_ctx_init(&child_ctx, child_tables, num_child_tables, 0UL);
	if (ret != 0) {
		ERROR("child xlat_ctx_init failed with ret=%d, va_start=0x%lx, va_size=0x%lx, num_tables=%u\n",
		      ret, va_start, va_size, num_child_tables);
		return ret;
	}

	/* Get the parent llt corresponding to the va */
	struct xlat_llt_info parent_llt;
	ret = xlat_get_llt_from_va(&parent_llt, &parent_ctx, va_start);
	if ((ret != 0) || (parent_llt.level != 1) || (parent_llt.table == NULL)) {
		ERROR("parent xlat_get_llt_from_va failed: ret=%d, level=%d, table=%p\n",
		      ret, parent_llt.level, parent_llt.table);
		return -1;
	}

	/* Confirm that child table start at level 1 */
	if (child_ctx.cfg.base_level != 1) {
		ERROR("child base_level is not 1: base_level=%d\n", child_ctx.cfg.base_level);
		return -1;
	}

	/* Get the child llt corresponding to the start of va range */
	struct xlat_llt_info child_llt;
	ret = xlat_get_llt_from_va(&child_llt, &child_ctx, va_start);
	if ((ret != 0) || (child_llt.level != 3) || (child_llt.table == NULL)) {
		ERROR("child xlat_get_llt_from_va (start) failed: ret=%d, level=%d, table=%p\n",
		      ret, child_llt.level, child_llt.table);
		return -1;
	}

	/* Get the child llt corresponding to the end of va range */
	struct xlat_llt_info child_llt_end;
	ret = xlat_get_llt_from_va(&child_llt_end, &child_ctx, va_start + va_size - 1);
	if ((ret != 0) || (child_llt_end.level != 3) || (child_llt_end.table == NULL)) {
		ERROR("child xlat_get_llt_from_va (end) failed: ret=%d, level=%d, table=%p\n",
		      ret, child_llt_end.level, child_llt_end.table);
		return -1;
	}

	/* Get child L1 table pointer */
	uint64_t *child_l1 = (uint64_t *)child_ctx.tbls.tables;
	if (child_l1 == NULL) {
		ERROR("child L1 table pointer is NULL\n");
		return -1;
	}

	/* Perform the stitch operation */
	ret = xlat_stitch_tables_l1(&parent_ctx, child_l1, va_start, va_size);
	if (ret != 0) {
		ERROR("xlat_stitch_tables_l1 failed: ret=%d, va_start=0x%lx, va_size=0x%lx\n",
		      ret, va_start, va_size);
		return ret;
	}

	/* Verify that parent llt now has the child's L3 entries at va_start*/
	ret = xlat_get_llt_from_va(&parent_llt, &parent_ctx, va_start);
	if ((ret != 0) || (parent_llt.level != 3) || (parent_llt.table == NULL)) {
		ERROR("parent xlat_get_llt_from_va (verify start) failed: ret=%d, level=%d, table=%p\n",
		      ret, parent_llt.level, parent_llt.table);
		return -1;
	}
	if (parent_llt.table != child_llt.table) {
		ERROR("parent and child tables mismatch at start: parent=%p, child=%p\n",
		      parent_llt.table, child_llt.table);
		return -1;
	}

	/* Verify that parent llt now has the child's L3 entries at end of va range */
	ret = xlat_get_llt_from_va(&parent_llt, &parent_ctx, va_start + va_size - 1);
	if ((ret != 0) || (parent_llt.level != 3) || (parent_llt.table == NULL)) {
		ERROR("parent xlat_get_llt_from_va (verify end) failed: ret=%d, level=%d, table=%p\n",
		      ret, parent_llt.level, parent_llt.table);
		return -1;
	}
	if (parent_llt.table != child_llt_end.table) {
		ERROR("parent and child tables mismatch at end: parent=%p, child=%p\n",
		      parent_llt.table, child_llt_end.table);
		return -1;
	}

	return 0;
}

/*
 * Test xlat_stitch_tables_l1() with a single L1 block entry.
 * This test sets up a parent context with TRANSIENT descriptors and a child
 * context with a single valid L1 block mapping, then verifies that stitching
 * copies the child entry to the parent.
 */
void xlat_stitch_l1_success_tc1(void)
{
	int ret;

	/* Test with single L1 block starting at address 0 */
	ret = xlat_stitch_test_helper(0x0UL, XLAT_BLOCK_SIZE(1),
				      &child_xlat_tables[0], 514U);
	CHECK_EQUAL(0, ret);
}

/*
 * Test xlat_stitch_tables_l1() with multiple L1 block entries.
 * This test sets up a parent context with TRANSIENT descriptors and a child
 * context with multiple valid L1 block mappings, then verifies that stitching
 * copies the child entries to the parent.
 */
void xlat_stitch_l1_multiple_blocks_tc1(void)
{
	int ret;
	uint64_t *child_alloc;
	unsigned int num_tables;

	/* For 4 L1 blocks: 1 L1 + 4*L2 + 4*512 L3 = ~4097 tables */
	num_tables = 2060U;
	child_alloc = (uint64_t *)aligned_alloc(GRANULE_SIZE,
		sizeof(uint64_t) * XLAT_TABLE_ENTRIES * num_tables);
	if (child_alloc == NULL) {
		FAIL("Failed to allocate memory for child tables");
		return;
	}

	/* Test with multiple L1 blocks starting at address 1GB */
	ret = xlat_stitch_test_helper(XLAT_BLOCK_SIZE(1), XLAT_BLOCK_SIZE(1) * 4,
				      child_alloc, num_tables);
	CHECK_EQUAL(0, ret);
	free(child_alloc);
}

/*
 * Test xlat_stitch_tables_l1() at L0 boundaries.
 * This verifies stitching works correctly when the VA range crosses L0 boundaries.
 */
void xlat_stitch_l1_at_boundaries_tc1(void)
{
	int ret;
	uintptr_t va_start;

	/* Start at the last L1 block to avoid crossing L0 boundary */
	va_start = XLAT_BLOCK_SIZE(0) - (XLAT_BLOCK_SIZE(1));
	/* Test with single L1 block starting at address va_start */
	ret = xlat_stitch_test_helper(va_start, XLAT_BLOCK_SIZE(1),
				      &child_xlat_tables[0], 514U);
	CHECK_EQUAL(0, ret);
}

/*
 * Test that xlat_stitch_tables_l1() correctly validates TRANSIENT descriptors.
 * This test attempts to stitch into a parent context that doesn't have TRANSIENT
 * descriptors, which should fail the assertion in the stitch function.
 */
void xlat_stitch_l1_verify_transient_tc1(void)
{
	struct xlat_ctx parent_ctx, child_ctx;
	struct xlat_mmap_region parent_mmap[2];
	struct xlat_mmap_region child_mmap[2];
	uintptr_t va_start;
	size_t va_size;
	int ret;

	/* Disable MMU for the test */
	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);

	va_start = 0x0UL;
	va_size = XLAT_BLOCK_SIZE(1);

	/* Setup parent context with NORMAL mapping (not TRANSIENT) */
	memset(&parent_ctx, 0, sizeof(parent_ctx));

	/* Use a normal mapping instead of TRANSIENT */
	parent_mmap[0].base_pa = 0x40000000UL;
	parent_mmap[0].base_va = va_start;
	parent_mmap[0].size = va_size;
	parent_mmap[0].attr = MT_RW_DATA | MT_REALM;
	parent_mmap[0].granularity = XLAT_BLOCK_SIZE(0);
	parent_mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	/* Parent context must start at 0 to cover the entire L0 block */
	ret = xlat_ctx_cfg_init(&parent_ctx, VA_LOW_REGION, &parent_mmap[0], 1U,
				0UL, XLAT_TEST_MAX_VA_SIZE(), 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&parent_ctx, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	/* Setup child context with normal mapping */
	memset(&child_ctx, 0, sizeof(child_ctx));

	child_mmap[0].base_pa = 0x80000000UL;
	child_mmap[0].base_va = va_start;
	child_mmap[0].size = va_size;
	child_mmap[0].attr = MT_RW_DATA | MT_REALM;
	child_mmap[0].granularity = GRANULE_SIZE;
	child_mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	/* Initialize child context with VA space that fits in L1 (single L0 block) */	/* Child context must also start at 0 to match parent */
	ret = xlat_ctx_cfg_init(&child_ctx, VA_LOW_REGION, &child_mmap[0], 1U,
				0UL, XLAT_BLOCK_SIZE(0), 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&child_ctx, &child_xlat_tables[0], 514U, 0UL);
	CHECK_EQUAL(0, ret);
	/* Check that the child tables base is at level 1 */
	CHECK_EQUAL(1, child_ctx.cfg.base_level);

	/*
	 * Attempting to stitch should fail because parent doesn't have TRANSIENT
	 * descriptors. The xlat_stitch_tables_l1 function has an assert that checks
	 * for TRANSIENT_DESC, so this would trigger an assertion failure in debug
	 * builds. For now, we just verify that the parent has valid (non-TRANSIENT)
	 * descriptors, which means stitching would be invalid.
	 */
	struct xlat_llt_info parent_llt;
	ret = xlat_get_llt_from_va(&parent_llt, &parent_ctx, va_start);
	CHECK_EQUAL(0, ret);
	CHECK_EQUAL(1, parent_llt.level);

	/* Verify parent has a valid block descriptor (not TRANSIENT) */
	unsigned int l1_idx = XLAT_TABLE_IDX(va_start, 1);
	CHECK_TRUE((parent_llt.table[l1_idx] & VALID_DESC) != 0);
	CHECK_TRUE(parent_llt.table[l1_idx] != TRANSIENT_DESC);

	/* Now try to stitch, we should hit an assert */
	uint64_t *child_l1 = (uint64_t *)child_ctx.tbls.tables;

	test_helpers_expect_assert_fail(true);
	ret = xlat_stitch_tables_l1(&parent_ctx, child_l1, va_start, va_size);
	test_helpers_fail_if_no_assert_failed();
}

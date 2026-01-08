/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>
#include <xlat_tests_base.h>

extern "C" {
#include <arch_helpers.h>
#include <debug.h>
#include <host_utils.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
#include <xlat_contexts.h>
#include <xlat_defs.h>
#include <xlat_tables.h>
#include <xlat_test_defs.h>
#include <xlat_test_helpers.h>
}

TEST_GROUP(xlat_va_alloc_tests) {
	TEST_SETUP()
	{
		xlat_test_setup(LPA2_DISABLED);
	}

	TEST_TEARDOWN()
	{}
};

TEST(xlat_va_alloc_tests, xlat_map_l3_region_basic_TC1)
{
	xlat_map_l3_region_basic_tc1();
}

TEST(xlat_va_alloc_tests, xlat_map_l3_region_basic_TC2)
{
	xlat_map_l3_region_basic_tc2();
}

TEST(xlat_va_alloc_tests, xlat_map_l3_region_basic_TC3)
{
	xlat_map_l3_region_basic_tc3();
}

TEST(xlat_va_alloc_tests, xlat_map_l3_region_errors_TC1)
{
	xlat_map_l3_region_errors_tc1();
}

TEST(xlat_va_alloc_tests, xlat_map_l3_region_errors_TC2)
{
	xlat_map_l3_region_errors_tc2();
}

TEST(xlat_va_alloc_tests, xlat_unmap_l3_region_basic_TC1)
{
	xlat_unmap_l3_region_basic_tc1();
}

TEST(xlat_va_alloc_tests, xlat_unmap_l3_region_basic_TC2)
{
	xlat_unmap_l3_region_basic_tc2();
}

TEST(xlat_va_alloc_tests, xlat_unmap_l3_region_basic_TC3)
{
	xlat_unmap_l3_region_basic_tc3();
}

TEST(xlat_va_alloc_tests, xlat_unmap_l3_region_errors_TC1)
{
	xlat_unmap_l3_region_errors_tc1();
}

TEST(xlat_va_alloc_tests, xlat_va_alloc_boundaries_TC1)
{
	xlat_va_alloc_boundaries_tc1();
}

TEST(xlat_va_alloc_tests, xlat_va_alloc_boundaries_TC2)
{
	xlat_va_alloc_boundaries_tc2();
}

TEST(xlat_va_alloc_tests, xlat_va_alloc_boundaries_TC3)
{
	xlat_va_alloc_boundaries_tc3();
}

TEST(xlat_va_alloc_tests, xlat_va_alloc_flag_propagation_TC1)
{
	xlat_va_alloc_flag_propagation_tc1();
}

TEST(xlat_va_alloc_tests, xlat_va_alloc_multi_l2_TC1)
{
	xlat_va_alloc_multi_l2_tc1();
}

TEST(xlat_va_alloc_tests, xlat_va_alloc_table_shape_TC1)
{
	xlat_va_alloc_table_shape_tc1();
}

TEST(xlat_va_alloc_tests, xlat_va_alloc_multi_region_TC1)
{
	xlat_va_alloc_multi_region_tc1();
}

TEST(xlat_va_alloc_tests, xlat_va_alloc_multi_region_TC2)
{
	xlat_va_alloc_multi_region_tc2();
}

TEST(xlat_va_alloc_tests, xlat_va_alloc_search_reset_TC1)
{
	xlat_va_alloc_search_reset_tc1();
}

TEST(xlat_va_alloc_tests, xlat_va_alloc_exhaust_va_space_TC1)
{
	xlat_va_alloc_exhaust_va_space_tc1();
}

TEST(xlat_va_alloc_tests, xlat_va_alloc_va_end_boundary_TC1)
{
	xlat_va_alloc_va_end_boundary_tc1();
}

void xlat_map_l3_region_basic_tc1(void)
{
	/***********************************************************************
	 * TEST CASE 1:
	 *
	 * Test basic allocation of a single page in a context with transient
	 * VA space. Verify that the function returns success and a valid VA.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_va;
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();
	/* Create a transient region */
	mmap[0] = MAP_REGION_TRANSIENT(0UL, 16UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	/* Initialize context */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	/* Initialize context */
	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Try to allocate a single page */
	uintptr_t test_pa = 0x80000000UL;
	ret = xlat_map_l3_region(&ctx, test_pa, GRANULE_SIZE, MT_RW_DATA, &mapped_va);
	CHECK_EQUAL(0, ret);

	/* Verify the VA is in valid range */
	CHECK_TRUE(mapped_va >= cfg.base_va);
	CHECK_TRUE(mapped_va < (cfg.base_va + cfg.max_va_size));

	/* Verify alignment */
	CHECK_EQUAL(0UL, mapped_va & (GRANULE_SIZE - 1UL));

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_map_l3_region_basic_tc2(void)
{
	/***********************************************************************
	 * TEST CASE 2:
	 *
	 * Test allocation of multiple consecutive pages.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_vas[10];
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/* Create a transient region */
	mmap[0] = MAP_REGION_TRANSIENT(0UL, 10UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	/* Initialize context */
	 memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	 memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	 memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Allocate multiple pages */
	for (unsigned int i = 0; i < 10; i++) {
		uintptr_t test_pa = 0x80000000UL + (i * GRANULE_SIZE);
		ret = xlat_map_l3_region(&ctx, test_pa, GRANULE_SIZE,
					 MT_RW_DATA, &mapped_vas[i]);
		CHECK_EQUAL(0, ret);
		CHECK_EQUAL(0UL, mapped_vas[i] & (GRANULE_SIZE - 1UL));
	}

	/* Verify all VAs are unique */
	for (unsigned int i = 0; i < 10; i++) {
		for (unsigned int j = i + 1; j < 10; j++) {
			CHECK_FALSE(mapped_vas[i] == mapped_vas[j]);
		}
	}

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_map_l3_region_basic_tc3(void)
{
	/***********************************************************************
	 * TEST CASE 3:
	 *
	 * Test allocation of multi-page regions.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_va;
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	mmap[0] = MAP_REGION_TRANSIENT(0UL, 16UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	/* Initialize context */
	 memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	 memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	 memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Allocate a 64KB region (16 pages) */
	size_t alloc_size = 16 * GRANULE_SIZE;
	uintptr_t test_pa = 0x80000000UL;
	ret = xlat_map_l3_region(&ctx, test_pa, alloc_size, MT_RW_DATA, &mapped_va);
	CHECK_EQUAL(0, ret);

	/* Verify alignment */
	CHECK_EQUAL(0UL, mapped_va & (GRANULE_SIZE - 1UL));

	/* Verify the VA range is valid */
	CHECK_TRUE(mapped_va >= cfg.base_va);
	CHECK_TRUE((mapped_va + alloc_size) <= (cfg.base_va + cfg.max_va_size));

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_map_l3_region_errors_tc1(void)
{
	/***********************************************************************
	 * TEST CASE 1:
	 *
	 * Test error handling for invalid parameters.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_va;
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	mmap[0] = MAP_REGION_TRANSIENT(0x1000UL, 16UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	/* Initialize context */
	 memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	 memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	 memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Test unaligned PA */
	ret = xlat_map_l3_region(&ctx, 0x80000001UL, GRANULE_SIZE,
				 MT_RW_DATA, &mapped_va);
	CHECK_EQUAL(-EFAULT, ret);

	/* Test unaligned size */
	ret = xlat_map_l3_region(&ctx, 0x80000000UL, GRANULE_SIZE + 1,
				 MT_RW_DATA, &mapped_va);
	CHECK_EQUAL(-EFAULT, ret);

	/* Test zero size */
	ret = xlat_map_l3_region(&ctx, 0x80000000UL, 0UL,
				 MT_RW_DATA, &mapped_va);
	CHECK_EQUAL(-EINVAL, ret);

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_map_l3_region_errors_tc2(void)
{
	/***********************************************************************
	 * TEST CASE 2:
	 *
	 * Test allocation exhaustion.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_va;
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();
	unsigned int successful_allocs = 0;

	/* Create a small transient region */
	size_t small_region = 64 * GRANULE_SIZE;
	mmap[0] = MAP_REGION_TRANSIENT(0UL, small_region, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	/* Initialize context */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Allocate pages until we run out of space */
	for (unsigned int i = 0; i < 100; i++) {
		uintptr_t test_pa = 0x80000000UL + (i * GRANULE_SIZE);
		ret = xlat_map_l3_region(&ctx, test_pa, GRANULE_SIZE,
					 MT_RW_DATA, &mapped_va);
		if (ret == 0) {
			successful_allocs++;
		} else {
			/* Should get -ENOMEM when exhausted */
			CHECK_EQUAL(-ENOMEM, ret);
			break;
		}
	}

	/* We should have been able to allocate upto small_region */
	CHECK_EQUAL(small_region, successful_allocs * GRANULE_SIZE);

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_unmap_l3_region_basic_tc1(void)
{
	/***********************************************************************
	 * TEST CASE 1:
	 *
	 * Test basic unmapping of a single page.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_va, mapped_va2;
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	mmap[0] = MAP_REGION_TRANSIENT(0UL, 16UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Allocate a page */
	uintptr_t test_pa = 0x80000000UL;
	ret = xlat_map_l3_region(&ctx, test_pa, GRANULE_SIZE, MT_RW_DATA, &mapped_va);
	CHECK_EQUAL(0, ret);

	/* Unmap the page */
	ret = xlat_unmap_l3_region(&ctx, mapped_va, GRANULE_SIZE);
	CHECK_EQUAL(0, ret);

	/* Reallocate - should succeed */
	ret = xlat_map_l3_region(&ctx, test_pa, GRANULE_SIZE, MT_RW_DATA, &mapped_va2);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_unmap_l3_region_basic_tc2(void)
{
	/***********************************************************************
	 * TEST CASE 2:
	 *
	 * Test unmapping of multiple pages.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_vas[5];
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	mmap[0] = MAP_REGION_TRANSIENT(0x1000UL, 5UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Allocate multiple pages */
	for (unsigned int i = 0; i < 5; i++) {
		uintptr_t test_pa = 0x80000000UL + (i * GRANULE_SIZE);
		ret = xlat_map_l3_region(&ctx, test_pa, GRANULE_SIZE,
					 MT_RW_DATA, &mapped_vas[i]);
		CHECK_EQUAL(0, ret);
	}

	/* Unmap all pages */
	for (unsigned int i = 0; i < 5; i++) {
		ret = xlat_unmap_l3_region(&ctx, mapped_vas[i], GRANULE_SIZE);
		CHECK_EQUAL(0, ret);
	}

	/* Reallocate - should succeed */
	for (unsigned int i = 0; i < 5; i++) {
		uintptr_t test_pa = 0x80000000UL + (i * GRANULE_SIZE);
		ret = xlat_map_l3_region(&ctx, test_pa, GRANULE_SIZE,
					 MT_RW_DATA, &mapped_vas[i]);
		CHECK_EQUAL(0, ret);
	}

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_unmap_l3_region_basic_tc3(void)
{
	/***********************************************************************
	 * TEST CASE 3:
	 *
	 * Test unmapping of multi-page regions.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_va, mapped_va2;
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	mmap[0] = MAP_REGION_TRANSIENT(0UL, 16UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};
	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Allocate a 64KB region (16 pages) */
	size_t alloc_size = 16 * GRANULE_SIZE;
	uintptr_t test_pa = 0x80000000UL;
	ret = xlat_map_l3_region(&ctx, test_pa, alloc_size, MT_RW_DATA, &mapped_va);
	CHECK_EQUAL(0, ret);

	/* Unmap the region */
	ret = xlat_unmap_l3_region(&ctx, mapped_va, alloc_size);
	CHECK_EQUAL(0, ret);

	/* Reallocate the same size - should succeed */
	ret = xlat_map_l3_region(&ctx, test_pa, alloc_size, MT_RW_DATA, &mapped_va2);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_unmap_l3_region_errors_tc1(void)
{
	/***********************************************************************
	 * TEST CASE 1:
	 *
	 * Test error handling for invalid parameters.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_va;
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	mmap[0] = MAP_REGION_TRANSIENT(0UL, 16UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Allocate a page first */
	uintptr_t test_pa = 0x80000000UL;
	ret = xlat_map_l3_region(&ctx, test_pa, GRANULE_SIZE, MT_RW_DATA, &mapped_va);
	CHECK_EQUAL(0, ret);

	/* Test unaligned VA */
	ret = xlat_unmap_l3_region(&ctx, mapped_va + 1, GRANULE_SIZE);
	CHECK_EQUAL(-EFAULT, ret);

	/* Test unaligned size */
	ret = xlat_unmap_l3_region(&ctx, mapped_va, GRANULE_SIZE + 1);
	CHECK_EQUAL(-EFAULT, ret);

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_va_alloc_boundaries_tc1(void)
{
	/***********************************************************************
	 * TEST CASE 1:
	 *
	 * Test allocation spanning L3 table boundaries.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_va;
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	mmap[0] = MAP_REGION_TRANSIENT(0UL, 513UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Allocate a region that spans L3 table boundary (513 pages) */
	size_t alloc_size = 513 * GRANULE_SIZE;
	uintptr_t test_pa = 0x80000000UL;
	ret = xlat_map_l3_region(&ctx, test_pa, alloc_size, MT_RW_DATA, &mapped_va);
	CHECK_EQUAL(0, ret);

	CHECK_EQUAL(0UL, mapped_va & (GRANULE_SIZE - 1UL));

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_va_alloc_boundaries_tc2(void)
{
	/***********************************************************************
	 * TEST CASE 2:
	 *
	 * Test fragmentation handling.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_vas[10];
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	mmap[0] = MAP_REGION_TRANSIENT(0UL, 10UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Allocate pages */
	for (unsigned int i = 0; i < 10; i++) {
		uintptr_t test_pa = 0x80000000UL + (i * GRANULE_SIZE);
		ret = xlat_map_l3_region(&ctx, test_pa, GRANULE_SIZE,
					 MT_RW_DATA, &mapped_vas[i]);
		CHECK_EQUAL(0, ret);
	}

	/* Free every other page to create fragmentation */
	for (unsigned int i = 0; i < 10; i += 2) {
		ret = xlat_unmap_l3_region(&ctx, mapped_vas[i], GRANULE_SIZE);
		CHECK_EQUAL(0, ret);
	}

	/* Allocate new pages - should find the freed slots */
	for (unsigned int i = 0; i < 5; i++) {
		uintptr_t test_pa = 0x90000000UL + (i * GRANULE_SIZE);
		uintptr_t new_va;
		ret = xlat_map_l3_region(&ctx, test_pa, GRANULE_SIZE,
					 MT_RW_DATA, &new_va);
		CHECK_EQUAL(0, ret);
	}

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_va_alloc_boundaries_tc3(void)
{
	/***********************************************************************
	 * TEST CASE 3:
	 *
	 * Test allocation at the end of VA space.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_va;
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();
	unsigned int alloc_count = 0;

	/* Create a small region to test boundary */
	size_t region_size = 32 * GRANULE_SIZE;
	mmap[0] = MAP_REGION_TRANSIENT(0UL, region_size, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Fill the entire VA space */
	for (unsigned int i = 0; i < 32; i++) {
		uintptr_t test_pa = 0x80000000UL + (i * GRANULE_SIZE);
		ret = xlat_map_l3_region(&ctx, test_pa, GRANULE_SIZE,
					 MT_RW_DATA, &mapped_va);
		if (ret == 0) {
			alloc_count++;
		}
	}

	/* Should have allocated pages */
	CHECK_TRUE(alloc_count > 0);

	/* Next allocation should fail */
	ret = xlat_map_l3_region(&ctx, 0xA0000000UL, GRANULE_SIZE,
				 MT_RW_DATA, &mapped_va);
	CHECK_EQUAL(-ENOMEM, ret);

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_va_alloc_flag_propagation_tc1(void)
{
	/***********************************************************************
	 * TEST CASE: VA_ALLOCATED Flag Propagation
	 *
	 * Test that VA_ALLOCATED flag is properly propagated to parent tables
	 * when allocating and deallocating VA space.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_vas[512];
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/* Create 2MB transient region (one L3 table = 512 pages) */
	mmap[0] = MAP_REGION_TRANSIENT(0UL, 512UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Get L3 table for VA 0 to check flags */
	struct xlat_llt_info llt;
	ret = xlat_get_llt_from_va(&llt, &ctx, 0UL);
	CHECK_EQUAL(0, ret);
	CHECK_EQUAL(XLAT_TABLE_LEVEL_MAX, llt.level);

	/* Initially, no entries should have VA_ALLOCATED_FLAG */
	uint64_t *l3_table = llt.table;
	for (unsigned int i = 0; i < 512; i++) {
		uint64_t desc = l3_table[i];
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) == 0ULL);
		CHECK_TRUE((desc & TRANSIENT_DESC) != 0ULL);
	}

	/* Allocate all 512 pages in the L3 table */
	for (unsigned int i = 0; i < 512; i++) {
		uintptr_t test_pa = 0x80000000UL + (i * GRANULE_SIZE);
		ret = xlat_map_l3_region(&ctx, test_pa, GRANULE_SIZE,
					 MT_RW_DATA, &mapped_vas[i]);
		CHECK_EQUAL(0, ret);
		CHECK_EQUAL(i * GRANULE_SIZE, mapped_vas[i]);
	}

	/* Now all L3 entries should have VA_ALLOCATED_FLAG set */
	for (unsigned int i = 0; i < 512; i++) {
		uint64_t desc = l3_table[i];
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) != 0ULL);
		CHECK_TRUE((desc & TRANSIENT_DESC) != 0ULL);
		CHECK_TRUE((desc & VALID_DESC) != 0ULL);
	}

	/* Check parent L2 table - it should have VA_ALLOCATED_FLAG set */
	uint64_t l2_desc;
	uint64_t *l2_table;
	unsigned int l2_idx;

	ret = xlat_test_helpers_get_tte_at_level(&ctx, 0UL, 2, &l2_desc, &l2_table, &l2_idx);
	LONGS_EQUAL(0, ret);
	CHECK_TRUE((l2_desc & DESC_MASK) == TABLE_DESC);
	CHECK_TRUE((l2_desc & VA_ALLOCATED_FLAG) != 0ULL);

	/* Unmap one page - L2 flag should be cleared */
	ret = xlat_unmap_l3_region(&ctx, mapped_vas[256], GRANULE_SIZE);
	CHECK_EQUAL(0, ret);

	/* L2 should no longer have VA_ALLOCATED_FLAG */
	ret = xlat_test_helpers_get_tte_at_level(&ctx, 0UL, 2, &l2_desc, &l2_table, &l2_idx);
	LONGS_EQUAL(0, ret);
	CHECK_TRUE((l2_desc & VA_ALLOCATED_FLAG) == 0ULL);

	/* L3 entry should have TRANSIENT_DESC but not VA_ALLOCATED_FLAG */
	uint64_t unmapped_desc = l3_table[256];
	CHECK_TRUE((unmapped_desc & TRANSIENT_DESC) != 0ULL);
	CHECK_TRUE((unmapped_desc & VA_ALLOCATED_FLAG) == 0ULL);
	CHECK_TRUE((unmapped_desc & VALID_DESC) == 0ULL);

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_va_alloc_multi_l2_tc1(void)
{
	/***********************************************************************
	 * TEST CASE: Multiple L2 Tables
	 *
	 * Test allocation spanning multiple L2 tables (> 2MB).
	 * Verify VA_ALLOCATED flag is set for all involved L2 tables.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_va;
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/* Create 8MB transient region (4 L3 tables = 4 * 2MB) */
	mmap[0] = MAP_REGION_TRANSIENT(0UL, 2048UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Allocate 6MB (3 L3 tables worth, spanning multiple L2 entries) */
	size_t alloc_size = 1536UL * GRANULE_SIZE; /* 6MB = 3 * 2MB */
	uintptr_t test_pa = 0x80000000UL;
	ret = xlat_map_l3_region(&ctx, test_pa, alloc_size, MT_RW_DATA, &mapped_va);
	CHECK_EQUAL(0, ret);
	CHECK_EQUAL(0UL, mapped_va);

	/* Verify all L3 tables have entries with VA_ALLOCATED_FLAG */
	for (size_t offset = 0; offset < alloc_size; offset += (512UL * GRANULE_SIZE)) {
		struct xlat_llt_info llt;
		ret = xlat_get_llt_from_va(&llt, &ctx, mapped_va + offset);
		CHECK_EQUAL(0, ret);
		CHECK_EQUAL(XLAT_TABLE_LEVEL_MAX, llt.level);

		/* Check some L3 entries in this table */
		uint64_t *l3_table = llt.table;
		for (unsigned int i = 0; i < 512; i++) {
			uint64_t desc = l3_table[i];
			CHECK_TRUE((desc & VA_ALLOCATED_FLAG) != 0ULL);
			CHECK_TRUE((desc & TRANSIENT_DESC) != 0ULL);
			CHECK_TRUE((desc & VALID_DESC) != 0ULL);
		}
	}

	/* Check L2 parent tables have VA_ALLOCATED_FLAG set */
	for (unsigned int i = 0; i < 3; i++) {
		uintptr_t va = i * 512UL * GRANULE_SIZE;
		uint64_t l2_desc;
		uint64_t *l2_table;
		unsigned int l2_idx;

		ret = xlat_test_helpers_get_tte_at_level(&ctx, va, 2, &l2_desc, &l2_table, &l2_idx);
		LONGS_EQUAL(0, ret);
		CHECK_TRUE((l2_desc & DESC_MASK) == TABLE_DESC);
		CHECK_TRUE((l2_desc & VA_ALLOCATED_FLAG) != 0ULL);
	}

	/* Unmap the allocation */
	ret = xlat_unmap_l3_region(&ctx, mapped_va, alloc_size);
	CHECK_EQUAL(0, ret);

	/* Verify L2 entries no longer have VA_ALLOCATED_FLAG */
	for (unsigned int i = 0; i < 3; i++) {
		uintptr_t va = i * 512UL * GRANULE_SIZE;
		uint64_t l2_desc;
		uint64_t *l2_table;
		unsigned int l2_idx;

		ret = xlat_test_helpers_get_tte_at_level(&ctx, va, 2, &l2_desc, &l2_table, &l2_idx);
		LONGS_EQUAL(0, ret);
		CHECK_TRUE((l2_desc & VA_ALLOCATED_FLAG) == 0ULL);
	}

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_va_alloc_table_shape_tc1(void)
{
	/***********************************************************************
	 * TEST CASE: Table Shape Validation
	 *
	 * Test that tables maintain correct shape after mapping and unmapping.
	 * Verify descriptors, flags, and table structure.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_va1;
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/* Create 2MB transient region */
	mmap[0] = MAP_REGION_TRANSIENT(0UL, 512UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Get L3 table to verify initial state */
	struct xlat_llt_info llt;
	ret = xlat_get_llt_from_va(&llt, &ctx, 0UL);
	CHECK_EQUAL(0, ret);
	uint64_t *l3_table = llt.table;

	/* Initial state: all entries should be TRANSIENT_DESC only */
	for (unsigned int i = 0; i < 512; i++) {
		uint64_t desc = l3_table[i];
		CHECK_EQUAL(TRANSIENT_DESC, desc);
	}

	/* Allocate contiguous region, then create gaps by unmapping */
	ret = xlat_map_l3_region(&ctx, 0x80000000UL, 35UL * GRANULE_SIZE,
				 MT_RW_DATA, &mapped_va1);
	CHECK_EQUAL(0, ret);
	CHECK_EQUAL(0UL, mapped_va1);

	/* Verify all entries allocated */
	for (unsigned int i = 0; i < 35; i++) {
		uint64_t desc = l3_table[i];
		CHECK_TRUE((desc & VALID_DESC) != 0ULL);
		CHECK_TRUE((desc & TRANSIENT_DESC) != 0ULL);
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) != 0ULL);
	}

	/* Unmap middle section to create gaps */
	ret = xlat_unmap_l3_region(&ctx, mapped_va1 + (10UL * GRANULE_SIZE), 5UL * GRANULE_SIZE);
	CHECK_EQUAL(0, ret);

	ret = xlat_unmap_l3_region(&ctx, mapped_va1 + (20UL * GRANULE_SIZE), 5UL * GRANULE_SIZE);
	CHECK_EQUAL(0, ret);

	/* Verify gaps are unallocated */
	for (unsigned int i = 10; i < 15; i++) {
		uint64_t desc = l3_table[i];
		CHECK_TRUE((desc & VALID_DESC) == 0ULL);
		CHECK_TRUE((desc & TRANSIENT_DESC) != 0ULL);
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) == 0ULL);
	}

	for (unsigned int i = 20; i < 25; i++) {
		uint64_t desc = l3_table[i];
		CHECK_TRUE((desc & VALID_DESC) == 0ULL);
		CHECK_TRUE((desc & TRANSIENT_DESC) != 0ULL);
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) == 0ULL);
	}

	/* Verify allocated regions remain */
	for (unsigned int i = 0; i < 10; i++) {
		uint64_t desc = l3_table[i];
		CHECK_TRUE((desc & VALID_DESC) != 0ULL);
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) != 0ULL);
	}

	for (unsigned int i = 15; i < 20; i++) {
		uint64_t desc = l3_table[i];
		CHECK_TRUE((desc & VALID_DESC) != 0ULL);
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) != 0ULL);
	}

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_va_alloc_multi_region_tc1(void)
{
	/***********************************************************************
	 * TEST CASE: Multiple TRANSIENT Regions
	 *
	 * Test with multiple non-overlapping TRANSIENT regions.
	 * Verify allocations work correctly across different regions.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[4];
	uintptr_t mapped_va1, mapped_va2, mapped_va3;
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/* Create 3 separate TRANSIENT regions with gaps */
	mmap[0] = MAP_REGION_TRANSIENT(0UL, 512UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = MAP_REGION_TRANSIENT(1024UL * GRANULE_SIZE, 512UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[2] = MAP_REGION_TRANSIENT(2048UL * GRANULE_SIZE, 512UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[3] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 3U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Allocate from first region */
	ret = xlat_map_l3_region(&ctx, 0x80000000UL, 500UL * GRANULE_SIZE,
				 MT_RW_DATA, &mapped_va1);
	CHECK_EQUAL(0, ret);
	CHECK_TRUE(mapped_va1 < (512UL * GRANULE_SIZE));

	/* Allocate from second region */
	ret = xlat_map_l3_region(&ctx, 0x80100000UL, 500UL * GRANULE_SIZE,
				 MT_RW_DATA, &mapped_va2);
	CHECK_EQUAL(0, ret);
	/* Should allocate from second region */
	CHECK_TRUE((mapped_va2 >= (1024UL * GRANULE_SIZE) && mapped_va2 < (1536UL * GRANULE_SIZE)));

	/* Allocate from third region */
	ret = xlat_map_l3_region(&ctx, 0x80200000UL, 500UL * GRANULE_SIZE,
				 MT_RW_DATA, &mapped_va3);
	CHECK_EQUAL(0, ret);

	/* Should allocate from third region */
	CHECK_TRUE((mapped_va3 >= (2048UL * GRANULE_SIZE) && mapped_va3 < (2560UL * GRANULE_SIZE)));

	/* Verify each allocation is correctly mapped */
	struct xlat_llt_info llt1, llt2, llt3;
	ret = xlat_get_llt_from_va(&llt1, &ctx, mapped_va1);
	CHECK_EQUAL(0, ret);

	ret = xlat_get_llt_from_va(&llt2, &ctx, mapped_va2);
	CHECK_EQUAL(0, ret);

	ret = xlat_get_llt_from_va(&llt3, &ctx, mapped_va3);
	CHECK_EQUAL(0, ret);

	/* Check first allocation entries */
	uint64_t *l3_table1 = llt1.table;
	unsigned int start_idx1 = (mapped_va1 - llt1.llt_base_va) / GRANULE_SIZE;
	for (unsigned int i = start_idx1; i < start_idx1 + 500; i++) {
		uint64_t desc = l3_table1[i];
		CHECK_TRUE((desc & VALID_DESC) != 0ULL);
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) != 0ULL);
	}

	/* Check second allocation entries */
	uint64_t *l3_table2 = llt2.table;
	unsigned int start_idx2 = (mapped_va2 - llt2.llt_base_va) / GRANULE_SIZE;
	for (unsigned int i = start_idx2; i < start_idx2 + 500; i++) {
		uint64_t desc = l3_table2[i];
		CHECK_TRUE((desc & VALID_DESC) != 0ULL);
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) != 0ULL);
	}

	/* Check third allocation entries */
	uint64_t *l3_table3 = llt3.table;
	unsigned int start_idx3 = (mapped_va3 - llt3.llt_base_va) / GRANULE_SIZE;
	for (unsigned int i = start_idx3; i < start_idx3 + 500; i++) {
		uint64_t desc = l3_table3[i];
		CHECK_TRUE((desc & VALID_DESC) != 0ULL);
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) != 0ULL);
	}

	/* Unmap allocations */
	ret = xlat_unmap_l3_region(&ctx, mapped_va1, 10UL * GRANULE_SIZE);
	CHECK_EQUAL(0, ret);

	ret = xlat_unmap_l3_region(&ctx, mapped_va2, 10UL * GRANULE_SIZE);
	CHECK_EQUAL(0, ret);

	ret = xlat_unmap_l3_region(&ctx, mapped_va3, 10UL * GRANULE_SIZE);
	CHECK_EQUAL(0, ret);

	/* Verify unmapped entries */
	for (unsigned int i = start_idx1; i < start_idx1 + 10; i++) {
		uint64_t desc = l3_table1[i];
		CHECK_EQUAL(TRANSIENT_DESC, desc);
	}

	for (unsigned int i = start_idx2; i < start_idx2 + 10; i++) {
		uint64_t desc = l3_table2[i];
		CHECK_EQUAL(TRANSIENT_DESC, desc);
	}

	for (unsigned int i = start_idx3; i < start_idx3 + 10; i++) {
		uint64_t desc = l3_table3[i];
		CHECK_EQUAL(TRANSIENT_DESC, desc);
	}

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_va_alloc_multi_region_tc2(void)
{
	/***********************************************************************
	 * TEST CASE: Multiple TRANSIENT Regions - Fragmentation
	 *
	 * Test allocation across multiple regions when first region
	 * becomes fragmented. Verify allocator finds space in other regions.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[3];
	uintptr_t mapped_vas[600];
	int ret;
	unsigned int alloc_count = 0;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/* Create 2 TRANSIENT regions */
	mmap[0] = MAP_REGION_TRANSIENT(0UL, 512UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = MAP_REGION_TRANSIENT(1024UL * GRANULE_SIZE, 512UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[2] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 2U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Fill first region completely */
	for (unsigned int i = 0; i < 512; i++) {
		uintptr_t test_pa = 0x80000000UL + (i * GRANULE_SIZE);
		ret = xlat_map_l3_region(&ctx, test_pa, GRANULE_SIZE,
					 MT_RW_DATA, &mapped_vas[alloc_count]);
		if (ret == 0) {
			CHECK_TRUE(mapped_vas[alloc_count] < (512UL * GRANULE_SIZE));
			alloc_count++;
		}
	}

	CHECK_EQUAL(512U, alloc_count);

	/* Next allocation should go to second region */
	uintptr_t next_va;
	ret = xlat_map_l3_region(&ctx, 0x90000000UL, GRANULE_SIZE,
				 MT_RW_DATA, &next_va);
	CHECK_EQUAL(0, ret);
	CHECK_TRUE(next_va >= (1024UL * GRANULE_SIZE));
	CHECK_TRUE(next_va < (1536UL * GRANULE_SIZE));

	/* Free some pages in first region to create fragmentation */
	ret = xlat_unmap_l3_region(&ctx, mapped_vas[100], GRANULE_SIZE);
	CHECK_EQUAL(0, ret);

	ret = xlat_unmap_l3_region(&ctx, mapped_vas[200], GRANULE_SIZE);
	CHECK_EQUAL(0, ret);

	/* Allocate 2 more pages - should use freed slots in first region */
	uintptr_t frag_va1, frag_va2;
	ret = xlat_map_l3_region(&ctx, 0xA0000000UL, GRANULE_SIZE,
				 MT_RW_DATA, &frag_va1);
	CHECK_EQUAL(0, ret);
	CHECK_TRUE(frag_va1 < (512UL * GRANULE_SIZE));

	ret = xlat_map_l3_region(&ctx, 0xA0001000UL, GRANULE_SIZE,
				 MT_RW_DATA, &frag_va2);
	CHECK_EQUAL(0, ret);
	CHECK_TRUE(frag_va2 < (512UL * GRANULE_SIZE));

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_va_alloc_search_reset_tc1(void)
{
	/***********************************************************************
	 * TEST CASE: Search Reset on Allocated Page
	 *
	 * Test that the VA search correctly resets when it encounters an
	 * allocated page in the middle of a potential consecutive sequence.
	 * This covers the case where consecutive_free is reset and candidate_va
	 * is advanced past the allocated page.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_va1, mapped_va2, mapped_va3;
	int ret;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/* Create TRANSIENT region */
	mmap[0] = MAP_REGION_TRANSIENT(0UL, 512UL * GRANULE_SIZE, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Allocate 3 pages at the beginning */
	ret = xlat_map_l3_region(&ctx, 0x80000000UL, 3UL * GRANULE_SIZE,
				 MT_RW_DATA, &mapped_va1);
	CHECK_EQUAL(0, ret);
	CHECK_EQUAL(0UL, mapped_va1);

	/* Allocate 1 page at next available location (page 3) */
	ret = xlat_map_l3_region(&ctx, 0x80010000UL, GRANULE_SIZE,
				 MT_RW_DATA, &mapped_va2);
	CHECK_EQUAL(0, ret);
	CHECK_EQUAL(3UL * GRANULE_SIZE, mapped_va2);

	/* Allocate 5 pages at next available location (pages 4-8) */
	ret = xlat_map_l3_region(&ctx, 0x80020000UL, 5UL * GRANULE_SIZE,
				 MT_RW_DATA, &mapped_va3);
	CHECK_EQUAL(0, ret);
	CHECK_EQUAL(4UL * GRANULE_SIZE, mapped_va3);

	/*
	 * Now we have: pages 0-2 (3), page 3 (1), pages 4-8 (5), pages 9+ free
	 * Unmap page 3 to create a gap: 0-2 allocated, 3 free, 4-8 allocated, 9+ free
	 */
	ret = xlat_unmap_l3_region(&ctx, mapped_va2, GRANULE_SIZE);
	CHECK_EQUAL(0, ret);

	/*
	 * Try to allocate 4 consecutive pages. The search should:
	 * 1. Start at VA 0, encounter allocated pages 0-2
	 * 2. Find 1 free page at offset 3 (consecutive_free = 1)
	 * 3. Encounter allocated page at offset 4 -> RESET
	 * 4. Reset: consecutive_free = 0, candidate_va = page 5
	 * 5. Continue from page 5, find allocated pages through 8
	 * 6. Find free pages starting at 9
	 * 7. Allocate 4 pages at offset 9-12
	 */
	uintptr_t mapped_va4;
	ret = xlat_map_l3_region(&ctx, 0x80030000UL, 4UL * GRANULE_SIZE,
				 MT_RW_DATA, &mapped_va4);
	CHECK_EQUAL(0, ret);
	CHECK_EQUAL(9UL * GRANULE_SIZE, mapped_va4);

	/* Verify the allocation pattern using xlat_get_llt_from_va */
	struct xlat_llt_info llt;
	ret = xlat_get_llt_from_va(&llt, &ctx, 0UL);
	CHECK_EQUAL(0, ret);
	uint64_t *l3_table = llt.table;

	/* Pages 0-2 should be allocated */
	for (unsigned int i = 0; i < 3; i++) {
		uint64_t desc = l3_table[i];
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) != 0ULL);
		CHECK_TRUE((desc & VALID_DESC) != 0ULL);
	}

	/* Page 3 should be free (unmapped) */
	CHECK_TRUE((l3_table[3] & VA_ALLOCATED_FLAG) == 0ULL);
	CHECK_TRUE((l3_table[3] & VALID_DESC) == 0ULL);

	/* Pages 4-8 should be allocated */
	for (unsigned int i = 4; i < 9; i++) {
		uint64_t desc = l3_table[i];
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) != 0ULL);
		CHECK_TRUE((desc & VALID_DESC) != 0ULL);
	}

	/* Pages 9-12 should be allocated (new allocation) */
	for (unsigned int i = 9; i < 13; i++) {
		uint64_t desc = l3_table[i];
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) != 0ULL);
		CHECK_TRUE((desc & VALID_DESC) != 0ULL);
	}

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_va_alloc_exhaust_va_space_tc1(void)
{
	/***********************************************************************
	 * TEST CASE: Exhaust VA Space Boundary
	 *
	 * Test exhausting the entire VA space by setting max_va_size to exactly
	 * 512 pages (1 L3 table) and allocating all available space.
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_va;
	int ret;

	/* Create VA space of exactly 512 pages (1 full L3 table = 2MB) */
	size_t va_space_size = 512UL * GRANULE_SIZE;
	mmap[0] = MAP_REGION_TRANSIENT(0UL, va_space_size, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	/* Set max_va_size to match the TRANSIENT region size exactly */
	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				va_space_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Allocate all 512 pages in the VA space */
	ret = xlat_map_l3_region(&ctx, 0x80000000UL, va_space_size,
				 MT_RW_DATA, &mapped_va);
	CHECK_EQUAL(0, ret);
	CHECK_EQUAL(0UL, mapped_va);

	/* Verify all pages are allocated */
	struct xlat_llt_info llt;
	ret = xlat_get_llt_from_va(&llt, &ctx, 0UL);
	CHECK_EQUAL(0, ret);
	uint64_t *l3_table = llt.table;

	for (unsigned int i = 0; i < 512; i++) {
		uint64_t desc = l3_table[i];
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) != 0ULL);
		CHECK_TRUE((desc & VALID_DESC) != 0ULL);
	}

	/*
	 * Try to allocate one more page. This should fail because:
	 * - All 512 pages (indices 0-511) are allocated
	 * - When searching, the loop checks page 512
	 * - page_va for index 512 = 512 * GRANULE_SIZE = va_end
	 * - should return -ENOMEM
	 */
	uintptr_t overflow_va;
	ret = xlat_map_l3_region(&ctx, 0x90000000UL, GRANULE_SIZE,
				 MT_RW_DATA, &overflow_va);
	CHECK_EQUAL(-ENOMEM, ret);

	/* Unmap one page in the middle to create a gap */
	ret = xlat_unmap_l3_region(&ctx, 256UL * GRANULE_SIZE, GRANULE_SIZE);
	CHECK_EQUAL(0, ret);

	/* Now allocation of 1 page should succeed in the freed slot */
	uintptr_t reuse_va;
	ret = xlat_map_l3_region(&ctx, 0xA0000000UL, GRANULE_SIZE,
				 MT_RW_DATA, &reuse_va);
	CHECK_EQUAL(0, ret);
	CHECK_EQUAL(256UL * GRANULE_SIZE, reuse_va);

	/* Verify we still can't allocate beyond the VA space */
	ret = xlat_map_l3_region(&ctx, 0xB0000000UL, GRANULE_SIZE,
				 MT_RW_DATA, &overflow_va);
	CHECK_EQUAL(-ENOMEM, ret);

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

void xlat_va_alloc_va_end_boundary_tc1(void)
{
	/***********************************************************************
	 * TEST CASE: VA End Boundary Check
	 *
	 * Test the early boundary check that occurs at the start of each loop
	 * iteration in find_available_va. This exercises the condition where
	 * va_offset advances (via skip or L3 table boundary) such that
	 * current_va >= va_end at the loop start, before walking tables.
	 *
	 * Strategy:
	 * 1. Create VA space slightly larger than 1 L3 table (e.g., 600 pages)
	 * 2. Create TRANSIENT region matching this size
	 * 3. Fully allocate first L3 table (512 pages)
	 * 4. Allocate remaining pages in second L3 table (88 pages)
	 * 5. Try to allocate more - search will:
	 *    - Scan first L3 table, all allocated, move to next
	 *    - Scan second L3 table, find allocated pages 0-87
	 *    - Find free pages 88-511 in second L3 table, but they're outside TRANSIENT region
	 *    - va_offset advances to next L3 boundary
	 *    - current_va >= va_end (max_va_size = 1024 pages)
	 *    - Hit boundary check and exit with -ENOMEM
	 ***********************************************************************/

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region mmap[2];
	uintptr_t mapped_va;
	int ret;

	/* Create VA space of 1024 pages (2 L3 tables) with TRANSIENT region of 600 pages */
	size_t max_va_size = 1024UL * GRANULE_SIZE;  /* 4MB */
	size_t transient_size = 600UL * GRANULE_SIZE; /* 2.4MB */
	mmap[0] = MAP_REGION_TRANSIENT(0UL, transient_size, GRANULE_SIZE);
	mmap[1] = (struct xlat_mmap_region){0, 0, 0, 0, 0};

	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	/* Set max_va_size larger than TRANSIENT region */
	ret = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &mmap[0], 1U, 0UL,
				max_va_size, 0UL);
	CHECK_EQUAL(0, ret);

	ret = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES, 0UL);
	CHECK_EQUAL(0, ret);

	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Allocate all 600 pages */
	ret = xlat_map_l3_region(&ctx, 0x80000000UL, transient_size,
				 MT_RW_DATA, &mapped_va);
	CHECK_EQUAL(0, ret);
	CHECK_EQUAL(0UL, mapped_va);

	/* Verify first L3 table (pages 0-511) is fully allocated */
	struct xlat_llt_info llt1;
	ret = xlat_get_llt_from_va(&llt1, &ctx, 0UL);
	CHECK_EQUAL(0, ret);
	uint64_t *l3_table1 = llt1.table;

	for (unsigned int i = 0; i < 512; i++) {
		uint64_t desc = l3_table1[i];
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) != 0ULL);
		CHECK_TRUE((desc & VALID_DESC) != 0ULL);
	}

	/* Verify second L3 table (pages 512-599) is partially allocated */
	struct xlat_llt_info llt2;
	ret = xlat_get_llt_from_va(&llt2, &ctx, 512UL * GRANULE_SIZE);
	CHECK_EQUAL(0, ret);
	uint64_t *l3_table2 = llt2.table;

	for (unsigned int i = 0; i < 88; i++) {
		uint64_t desc = l3_table2[i];
		CHECK_TRUE((desc & VA_ALLOCATED_FLAG) != 0ULL);
		CHECK_TRUE((desc & VALID_DESC) != 0ULL);
	}

	/* Remaining entries in second L3 table are outside TRANSIENT region */
	for (unsigned int i = 88; i < 512; i++) {
		uint64_t desc = l3_table2[i];
		/* These entries are not part of the TRANSIENT region */
		CHECK_TRUE((desc & TRANSIENT_DESC) == 0ULL);
	}

	/*
	 * Try to allocate one more page. The search will:
	 * 1. Start at va_offset = 0
	 * 2. Walk first L3 table, find all pages allocated
	 * 3. Advance: va_offset = round_up(1, 2MB) = 512 pages
	 * 4. Walk second L3 table, find all valid pages allocated
	 * 5. After scanning 88 allocated pages, reach unallocated at page 88
	 * 6. However, pages 88-511 are not TRANSIENT (not part of mmap region)
	 * 7. va_offset advances to next L3 boundary = 1024 pages
	 * 8. current_va = 0 + 1024*4K = 4MB = va_end (max_va_size limit)
	 * 9. if (current_va >= va_end) break
	 */
	uintptr_t overflow_va;
	ret = xlat_map_l3_region(&ctx, 0x90000000UL, GRANULE_SIZE,
				 MT_RW_DATA, &overflow_va);
	CHECK_EQUAL(-ENOMEM, ret);

	/* Unmap one page to verify the VA space tracking is correct */
	ret = xlat_unmap_l3_region(&ctx, 300UL * GRANULE_SIZE, GRANULE_SIZE);
	CHECK_EQUAL(0, ret);

	/* Now allocation should succeed in the freed slot */
	uintptr_t reuse_va;
	ret = xlat_map_l3_region(&ctx, 0xA0000000UL, GRANULE_SIZE,
				 MT_RW_DATA, &reuse_va);
	CHECK_EQUAL(0, ret);
	CHECK_EQUAL(300UL * GRANULE_SIZE, reuse_va);

	/* Verify overflow still fails */
	ret = xlat_map_l3_region(&ctx, 0xB0000000UL, GRANULE_SIZE,
				 MT_RW_DATA, &overflow_va);
	CHECK_EQUAL(-ENOMEM, ret);

	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);
}

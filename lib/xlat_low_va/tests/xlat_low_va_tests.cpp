/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <errno.h>
#include <host_harness.h>
#include <host_utils.h>
#include <sizes.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <xlat_defs_private.h>
#include <xlat_low_va.h>
#include <xlat_low_va_pvt.h>
#include <xlat_tables.h>
#include <xlat_tables_private.h>
#include <xlat_test_helpers.h>
#include <stdlib.h>
}

/* Import test groups from other files */
IMPORT_TEST_GROUP(xlat_low_va_setup);

/*
 * Test group for xlat_low_va basic functionality
 */
static struct xlat_low_va_info saved_low_va_info;

TEST_GROUP(xlat_low_va) {
	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start(false);
		test_helpers_expect_assert_fail(false);

		/* Save original low_va_info state */
		struct xlat_low_va_info *info = xlat_get_low_va_info();
		memcpy(&saved_low_va_info, info, sizeof(struct xlat_low_va_info));
	}

	TEST_TEARDOWN()
	{
		/* Restore original low_va_info state */
		struct xlat_low_va_info *info = xlat_get_low_va_info();
		memcpy(info, &saved_low_va_info, sizeof(struct xlat_low_va_info));
	}
};

/*
 * Test: xlat_get_low_va_info returns valid pointer
 */
TEST(xlat_low_va, xlat_get_low_va_info_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that xlat_get_low_va_info() returns a valid non-NULL
	 * pointer to the low VA info structure.
	 ******************************************************************/

	struct xlat_low_va_info *info = xlat_get_low_va_info();

	CHECK_TRUE(info != NULL);
	CHECK_TRUE(info->low_va_regions_capacity == TOTAL_MMAP_REGIONS);
}

/*
 * Test: xlat_low_va_shared_buf_va returns valid address
 */
TEST(xlat_low_va, xlat_low_va_shared_buf_va_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that xlat_low_va_shared_buf_va() returns a non-zero
	 * address that is aligned to page size.
	 ******************************************************************/

	uintptr_t shared_buf_va = xlat_low_va_shared_buf_va();

	CHECK_TRUE(shared_buf_va != 0UL);
	CHECK_TRUE(ALIGNED(shared_buf_va, SZ_4K));
}

/*
 * Test: xlat_low_va_get_dyn_va_base returns valid address
 */
TEST(xlat_low_va, xlat_low_va_get_dyn_va_base_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that xlat_low_va_get_dyn_va_base() returns a non-zero
	 * address that is properly aligned.
	 ******************************************************************/

	uintptr_t dyn_va_base = xlat_low_va_get_dyn_va_base();

	CHECK_TRUE(dyn_va_base != 0UL);
	/* Should be aligned to at least 1GB */
	CHECK_TRUE(ALIGNED(dyn_va_base, SZ_1G));
}

/*
 * Test: Low VA info structure contains valid region count
 */
TEST(xlat_low_va, xlat_low_va_info_regions_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that the low VA info structure contains a valid number
	 * of regions that doesn't exceed capacity.
	 ******************************************************************/

	struct xlat_low_va_info *info = xlat_get_low_va_info();

	CHECK_TRUE(info->low_va_regions_num > 0U);
	CHECK_TRUE(info->low_va_regions_num <= TOTAL_MMAP_REGIONS);
	CHECK_TRUE(info->low_va_regions_num <= info->low_va_regions_capacity);
}

/*
 * Test: Low VA info structure has valid dynamic VA pool configuration
 */
TEST(xlat_low_va, xlat_low_va_dyn_pool_config_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that the dynamic VA pool has valid configuration with
	 * non-zero base and size.
	 ******************************************************************/

	struct xlat_low_va_info *info = xlat_get_low_va_info();

	CHECK_TRUE(info->dyn_va_pool_base != 0UL);
	CHECK_TRUE(info->dyn_va_pool_size > 0U);
	CHECK_TRUE(ALIGNED(info->dyn_va_pool_size, SZ_1G));
}

/*
 * Test: Low VA regions are properly sorted by base VA
 */
TEST(xlat_low_va, xlat_low_va_regions_sorted_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that the low VA regions array is sorted by base_va
	 * in ascending order.
	 ******************************************************************/

	struct xlat_low_va_info *info = xlat_get_low_va_info();

	for (unsigned int i = 1U; i < info->low_va_regions_num; i++) {
		CHECK_TRUE(info->low_va_regions[i].base_va >=
			   info->low_va_regions[i - 1].base_va);
	}
}


/*
 * Test: xlat_low_va_map with all valid attribute combinations
 */
TEST(xlat_low_va, xlat_low_va_map_memory_types_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Map granules with all valid attribute combinations and verify
	 * the returned VAs are valid and distinct.
	 ******************************************************************/

	uintptr_t test_pas[4];
	uintptr_t vas[4];
	uint64_t attrs[4] = {
		MT_RW_DATA | MT_REALM,
		MT_RW_DEV | MT_REALM,
		MT_RO_DATA | MT_REALM,
		MT_RW_DEV | MT_NS
	};
	struct xlat_low_va_info *info = xlat_get_low_va_info();

	for (unsigned int i = 0U; i < 4U; i++) {
		test_pas[i] = host_util_get_granule_base() + ((i + 1UL) * GRANULE_SIZE);
	}

	/* Map with each attribute combination and verify */
	for (unsigned int i = 0U; i < 4U; i++) {
		vas[i] = xlat_low_va_map(GRANULE_SIZE, attrs[i], test_pas[i], false);
		CHECK_TRUE(vas[i] != 0UL);
		CHECK_TRUE(ALIGNED(vas[i], GRANULE_SIZE));
		CHECK_TRUE(vas[i] >= info->dyn_va_pool_base);
	}

	/* Verify all mappings are distinct */
	for (unsigned int i = 0U; i < 4U; i++) {
		for (unsigned int j = i + 1U; j < 4U; j++) {
			CHECK_TRUE(vas[i] != vas[j]);
		}
	}
}

/*
 * Test: xlat_low_va_map with invalid attribute - MT_CODE
 */
ASSERT_TEST(xlat_low_va, xlat_low_va_map_invalid_attr_code_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that xlat_low_va_map() fails assertion with MT_CODE.
	 ******************************************************************/

	uintptr_t test_pa = host_util_get_granule_base() + (10UL * GRANULE_SIZE);
	uintptr_t va;

	test_helpers_expect_assert_fail(true);
	va = xlat_low_va_map(GRANULE_SIZE, MT_CODE | MT_REALM, test_pa, false);
	(void)va;
	test_helpers_fail_if_no_assert_failed();
}

/*
 * Test: xlat_low_va_map with invalid attribute - MT_RW_DATA | MT_NS
 */
ASSERT_TEST(xlat_low_va, xlat_low_va_map_invalid_attr_rw_data_ns_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that xlat_low_va_map() fails assertion with MT_RW_DATA | MT_NS.
	 ******************************************************************/

	uintptr_t test_pa = host_util_get_granule_base() + (11UL * GRANULE_SIZE);
	uintptr_t va;

	test_helpers_expect_assert_fail(true);
	va = xlat_low_va_map(GRANULE_SIZE, MT_RW_DATA | MT_NS, test_pa, false);
	(void)va;
	test_helpers_fail_if_no_assert_failed();
}

/*
 * Test: xlat_low_va_map with invalid attribute - MT_RO_DATA | MT_NS
 */
ASSERT_TEST(xlat_low_va, xlat_low_va_map_invalid_attr_ro_data_ns_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that xlat_low_va_map() fails assertion with MT_RO_DATA | MT_NS.
	 ******************************************************************/

	uintptr_t test_pa = host_util_get_granule_base() + (12UL * GRANULE_SIZE);
	uintptr_t va;

	test_helpers_expect_assert_fail(true);
	va = xlat_low_va_map(GRANULE_SIZE, MT_RO_DATA | MT_NS, test_pa, false);
	(void)va;
	test_helpers_fail_if_no_assert_failed();
}

/*
 * Test: xlat_low_va_map with clear_memory flag
 */
TEST(xlat_low_va, xlat_low_va_map_clear_memory_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Map a granule with clear_memory=false, verify memory is NOT
	 * cleared, then map with clear_memory=true and verify memory
	 * IS cleared.
	 ******************************************************************/

	uintptr_t test_pa1 = host_util_get_granule_base() + GRANULE_SIZE;
	uintptr_t va1;
	struct xlat_low_va_info *info = xlat_get_low_va_info();
	uint64_t *mem_ptr;
	const uint64_t pattern = 0xDEADBEEFCAFEBABEUL;
	bool has_nonzero = false;
	bool pattern_intact = true;
	bool all_zeros = true;

	/* Write non-zero pattern to physical memory */
	mem_ptr = (uint64_t *)test_pa1;
	for (size_t i = 0UL; i < (GRANULE_SIZE / sizeof(uint64_t)); i++) {
		mem_ptr[i] = pattern;
	}

	/* Map with clear_memory=false */
	va1 = xlat_low_va_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM, test_pa1, false);

	CHECK_TRUE(va1 != 0UL);
	CHECK_TRUE(ALIGNED(va1, GRANULE_SIZE));
	CHECK_TRUE(va1 >= info->dyn_va_pool_base);

	/* Verify the memory is NOT cleared and pattern is intact */
	mem_ptr = (uint64_t *)test_pa1;
	for (size_t i = 0UL; i < (GRANULE_SIZE / sizeof(uint64_t)); i++) {
		if (mem_ptr[i] != 0UL) {
			has_nonzero = true;
		}
		if (mem_ptr[i] != pattern) {
			pattern_intact = false;
		}
		if (has_nonzero && !pattern_intact) {
			break;
		}
	}
	CHECK_TRUE(has_nonzero);
	CHECK_TRUE(pattern_intact);

	/* Map with clear_memory=true */
	va1 = xlat_low_va_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM, test_pa1, true);

	CHECK_TRUE(va1 != 0UL);
	CHECK_TRUE(ALIGNED(va1, GRANULE_SIZE));
	CHECK_TRUE(va1 >= info->dyn_va_pool_base);

	/* Verify the memory IS cleared (all zeros) */
	mem_ptr = (uint64_t *)test_pa1;
	for (size_t i = 0UL; i < (GRANULE_SIZE / sizeof(uint64_t)); i++) {
		if (mem_ptr[i] != 0UL) {
			all_zeros = false;
			break;
		}
	}
	CHECK_TRUE(all_zeros);
}

/*
 * Test: xlat_low_va_map multiple distinct mappings
 */
TEST(xlat_low_va, xlat_low_va_map_multiple_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Map multiple granules and verify each gets a unique VA.
	 * Additionally, validate that the translation descriptors have
	 * been properly modified with the correct PA mappings.
	 * Unmap all the VAs at the end and verify unmapping succeeds.
	 ******************************************************************/

	uintptr_t test_pas[3] = { 0x10000UL, 0x20000UL, 0x30000UL };
	uintptr_t vas[3];
	struct xlat_low_va_info *info = xlat_get_low_va_info();
	uint64_t ttes[3];
	uint64_t *table_ptr;
	int level;
	unsigned int index;
	int ret;

	for (unsigned int i = 0U; i < 3U; i++) {
		vas[i] = xlat_low_va_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM,
					    test_pas[i], false);
		CHECK_TRUE(vas[i] != 0UL);
	}

	for (unsigned int i = 0U; i < 3U; i++) {
		for (unsigned int j = i + 1; j < 3U; j++) {
			CHECK_TRUE(vas[i] != vas[j]);
		}

		ret = xlat_test_helpers_table_walk(&info->dyn_va_ctx, vas[i],
						   &ttes[i], &table_ptr, &level, &index);
		CHECK_EQUAL(0, ret);
		CHECK_EQUAL(XLAT_TABLE_LEVEL_MAX, level);
		CHECK_TRUE((ttes[i] & DESC_MASK) == PAGE_DESC);
		CHECK_EQUAL(test_pas[i], xlat_get_oa_from_tte(ttes[i]));
	}

	for (unsigned int i = 0U; i < 3U; i++) {
		for (unsigned int j = i + 1; j < 3U; j++) {
			CHECK_TRUE(ttes[i] != ttes[j]);
		}

		ret = xlat_low_va_unmap(vas[i], GRANULE_SIZE);
		CHECK_EQUAL(0, ret);
	}
}

/*
 * Test: xlat_low_va_map exhausts VA pool
 */
TEST(xlat_low_va, xlat_low_va_map_exhaust_pool_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Map granules until the VA pool is exhausted, then verify that
	 * the next map operation fails.
	 ******************************************************************/

	struct xlat_low_va_info *info = xlat_get_low_va_info();
	size_t pool_size = info->dyn_va_pool_size;
	/* Map in larger blocks for efficiency */
	size_t block_size = 512UL * SZ_1M;
	size_t max_blocks = (pool_size + block_size - 1) / block_size;

	/* Store VA and size for each mapping */
	struct mapping {
		uintptr_t va;
		size_t size;
	};

	struct mapping *mappings = (struct mapping *)malloc(max_blocks * sizeof(struct mapping));
	uintptr_t test_pa_base = 0x10000UL;
	uintptr_t va;
	size_t mapped_count = 0U;
	size_t total_mapped_size = 0U;
	int ret;

	CHECK_TRUE(mappings != NULL);

	/* Map large blocks until we exhaust the VA pool */
	for (size_t i = 0UL; i < max_blocks; i++) {
		uintptr_t test_pa = test_pa_base + total_mapped_size;
		va = xlat_low_va_map(block_size, MT_RW_DATA | MT_REALM, test_pa, false);
		if (va == 0UL) {
			/* Pool exhausted, this is expected */
			break;
		}
		mappings[mapped_count].va = va;
		mappings[mapped_count].size = block_size;
		mapped_count++;
		total_mapped_size += block_size;
	}

	/* Verify we mapped a reasonable amount */
	CHECK_TRUE(mapped_count > 0U);
	CHECK_TRUE(total_mapped_size > 0U);

	/* Try to map one more block - this should fail (return 0) */
	va = xlat_low_va_map(block_size, MT_RW_DATA | MT_REALM,
			     test_pa_base + total_mapped_size, false);
	CHECK_EQUAL(0UL, va); /* Should fail when pool is exhausted */

	/* Unmap all the blocks to clean up */
	for (size_t i = 0UL; i < mapped_count; i++) {
		ret = xlat_low_va_unmap(mappings[i].va, mappings[i].size);
		CHECK_EQUAL(0, ret);
	}

	free(mappings);
}

/*
 * Test: xlat_low_va_unmap with partial and complete unmapping
 */
TEST(xlat_low_va, xlat_low_va_unmap_remap_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Test unmapping and remapping functionality:
	 * 1. Map 4 granules individually
	 * 2. Unmap the 3rd granule - should succeed
	 * 3. Map the 3rd granule again
	 * 4. Unmap all 4 granules as a block - should succeed
	 ******************************************************************/

	uintptr_t test_pa_base = host_util_get_granule_base() + GRANULE_SIZE;
	uintptr_t va[4];
	int ret;

	/* Step 1: Map 4 separate granules individually */
	for (unsigned int i = 0U; i < 4U; i++) {
		va[i] = xlat_low_va_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM,
					test_pa_base + (i * GRANULE_SIZE), false);
		CHECK_TRUE(va[i] != 0UL);
	}

	/* Verify the VAs are contiguous */
	for (unsigned int i = 1U; i < 4U; i++) {
		CHECK_EQUAL(va[0] + (i * GRANULE_SIZE), va[i]);
	}

	/* Step 2: Unmap the 3rd granule (index 2) - should succeed */
	ret = xlat_low_va_unmap(va[2], GRANULE_SIZE);
	CHECK_EQUAL(0, ret);

	/* Step 3: Map the 3rd granule again */
	uintptr_t va_third = xlat_low_va_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM,
					     test_pa_base + (2UL * GRANULE_SIZE), false);
	CHECK_TRUE(va_third != 0UL);
	CHECK_EQUAL(va[2], va_third); /* Should get the same VA */

	/* Step 4: Unmap all 4 granules as a block - should succeed now */
	ret = xlat_low_va_unmap(va[0], 4UL * GRANULE_SIZE);
	CHECK_EQUAL(0, ret);
}

/*
 * Test: xlat_low_va_mmu_cfg function succeeds
 */
TEST(xlat_low_va, xlat_low_va_mmu_cfg_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that xlat_low_va_mmu_cfg() succeeds when called with
	 * properly initialized context.
	 ******************************************************************/

	int ret;

	/* Disable MMU */
	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);

	/* MMU is already configured by test_helpers_rmm_start(), so this
	 * should succeed (idempotent operation) */
	ret = xlat_low_va_mmu_cfg();

	CHECK_EQUAL(0, ret);
}

/*
 * Test: xlat_low_va_map with zero PA should fail
 */
ASSERT_TEST(xlat_low_va, xlat_low_va_map_zero_pa_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that xlat_low_va_map() fails assertion with zero PA.
	 ******************************************************************/

	uintptr_t va;

	test_helpers_expect_assert_fail(true);
	va = xlat_low_va_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM, 0UL, false);
	(void)va; /* Suppress unused warning */
	test_helpers_fail_if_no_assert_failed();
}

/*
 * Test: xlat_low_va_map with unaligned PA should fail
 */
ASSERT_TEST(xlat_low_va, xlat_low_va_map_unaligned_pa_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that xlat_low_va_map() fails assertion with unaligned PA.
	 ******************************************************************/

	uintptr_t test_pa = host_util_get_granule_base() + 0x100; /* Misaligned */
	uintptr_t va;

	test_helpers_expect_assert_fail(true);
	va = xlat_low_va_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM, test_pa, false);
	(void)va; /* Suppress unused warning */
	test_helpers_fail_if_no_assert_failed();
}

/*
 * Test: Verify all expected common regions are present
 */
TEST(xlat_low_va, xlat_low_va_common_regions_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that all common regions (APP, CODE, RO, RW, SHARED,
	 * VA_POOL) are present in the regions array.
	 ******************************************************************/

	struct xlat_low_va_info *info = xlat_get_low_va_info();
	unsigned int region_count = 0U;

	/* Check that we have at least the common regions */
	CHECK_TRUE(info->low_va_regions_num >= COMMON_REGIONS);

	/*
	 * Note: Since regions are sorted by base_va, we can't rely on
	 * the original enum order. Just verify we have valid regions.
	 */
	for (unsigned int i = 0U; i < info->low_va_regions_num; i++) {
		if (info->low_va_regions[i].size > 0U) {
			region_count++;
		}
	}

	CHECK_TRUE(region_count >= COMMON_REGIONS);
}

/*
 * Test: Comprehensive validation of sort_mmap_region_array
 */
TEST(xlat_low_va, comprehensive_sort_validation_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Comprehensive test validating sort_mmap_region_array handles:
	 * - Empty arrays
	 * - Single element arrays
	 * - Already sorted arrays
	 * - Reverse sorted arrays
	 * - Random order arrays
	 * - Duplicate base_va values (stable sort)
	 * - Field preservation
	 * - Large address values
	 ******************************************************************/

	/* Test 1: Empty array - should not crash */
	struct xlat_mmap_region empty_regions[1];
	sort_mmap_region_array(empty_regions, 0U);

	/* Test 2: Single region - should remain unchanged */
	struct xlat_mmap_region single_region[1] = {
		{ .base_pa = 0x1000, .base_va = 0x5000, .size = SZ_4K,
		  .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE }
	};
	sort_mmap_region_array(single_region, 1U);
	CHECK_EQUAL(0x5000, single_region[0].base_va);
	CHECK_EQUAL(0x1000, single_region[0].base_pa);

	/* Test 3: Already sorted array - should remain sorted */
	struct xlat_mmap_region sorted_regions[5] = {
		{ .base_pa = 0x1000, .base_va = 0x1000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x2000, .base_va = 0x2000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x3000, .base_va = 0x3000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x4000, .base_va = 0x4000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x5000, .base_va = 0x5000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE }
	};
	sort_mmap_region_array(sorted_regions, 5U);
	for (unsigned int i = 0U; i < 5U; i++) {
		CHECK_EQUAL((0x1000 + i * 0x1000), sorted_regions[i].base_va);
	}

	/* Test 4: Reverse sorted array - worst case for insertion sort */
	struct xlat_mmap_region reverse_regions[5] = {
		{ .base_pa = 0x5000, .base_va = 0x5000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x4000, .base_va = 0x4000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x3000, .base_va = 0x3000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x2000, .base_va = 0x2000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x1000, .base_va = 0x1000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE }
	};
	sort_mmap_region_array(reverse_regions, 5U);
	for (unsigned int i = 0U; i < 5U; i++) {
		CHECK_EQUAL((0x1000 + i * 0x1000), reverse_regions[i].base_va);
	}

	/* Test 5: Random order */
	struct xlat_mmap_region random_regions[7] = {
		{ .base_pa = 0x9000, .base_va = 0x9000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x2000, .base_va = 0x2000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x7000, .base_va = 0x7000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x1000, .base_va = 0x1000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x5000, .base_va = 0x5000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x3000, .base_va = 0x3000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x8000, .base_va = 0x8000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE }
	};
	sort_mmap_region_array(random_regions, 7U);
	uintptr_t expected_vas[7] = {0x1000, 0x2000, 0x3000, 0x5000, 0x7000, 0x8000, 0x9000};
	for (unsigned int i = 0U; i < 7U; i++) {
		CHECK_EQUAL(expected_vas[i], random_regions[i].base_va);
	}

	/* Test 6: Field preservation */
	struct xlat_mmap_region field_regions[3] = {
		{ .base_pa = 0xA000, .base_va = 0x30000, .size = SZ_64K, .attr = MT_RO_DATA | MT_REALM, .granularity = SZ_64K },
		{ .base_pa = 0xB000, .base_va = 0x10000, .size = SZ_16K, .attr = MT_RW_DEV | MT_NS, .granularity = SZ_4K },
		{ .base_pa = 0xC000, .base_va = 0x20000, .size = SZ_16K, .attr = MT_CODE | MT_REALM, .granularity = SZ_16K }
	};
	sort_mmap_region_array(field_regions, 3U);
	/* Expected order after sorting by base_va: 0x10000, 0x20000, 0x30000 */
	uintptr_t expected_base_va[3] = {0x10000, 0x20000, 0x30000};
	uintptr_t expected_base_pa[3] = {0xB000, 0xC000, 0xA000};
	size_t expected_size[3] = {SZ_16K, SZ_16K, SZ_64K};
	uint64_t expected_attr[3] = {MT_RW_DEV | MT_NS, MT_CODE | MT_REALM, MT_RO_DATA | MT_REALM};
	size_t expected_granularity[3] = {SZ_4K, SZ_16K, SZ_64K};

	for (unsigned int i = 0U; i < 3U; i++) {
		CHECK_EQUAL(expected_base_va[i], field_regions[i].base_va);
		CHECK_EQUAL(expected_base_pa[i], field_regions[i].base_pa);
		CHECK_EQUAL(expected_size[i], field_regions[i].size);
		CHECK_EQUAL(expected_attr[i], field_regions[i].attr);
		CHECK_EQUAL(expected_granularity[i], field_regions[i].granularity);
	}


	/* Test 7: Large address values */
	struct xlat_mmap_region large_regions[4] = {
		{ .base_pa = 0x1000000000UL, .base_va = 0xFFFF00000000UL, .size = SZ_1M, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x2000000000UL, .base_va = 0x0000000F0000UL, .size = SZ_1M, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x3000000000UL, .base_va = 0x2000000000UL, .size = SZ_1M, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x4000000000UL, .base_va = 0x0FFFFF0000UL, .size = SZ_1M, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE }
	};
	sort_mmap_region_array(large_regions, 4);

	uintptr_t expected_large_vas[4] = {
		0x0000000F0000UL,
		0x0FFFFF0000UL,
		0x2000000000UL,
		0xFFFF00000000UL
	};
	uintptr_t expected_large_pas[4] = {
		0x2000000000UL,
		0x4000000000UL,
		0x3000000000UL,
		0x1000000000UL
	};
	for (unsigned int i = 0U; i < 4U; i++) {
		CHECK_EQUAL(expected_large_vas[i], large_regions[i].base_va);
		CHECK_EQUAL(expected_large_pas[i], large_regions[i].base_pa);
	}
}

/*
 * Test: sort_mmap_region_array with duplicate base_va values triggers assertion
 */
ASSERT_TEST(xlat_low_va, sort_duplicate_base_va_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that sort_mmap_region_array asserts when duplicate
	 * base_va values are detected in the array.
	 ******************************************************************/

	struct xlat_mmap_region dup_regions[3] = {
		{ .base_pa = 0x1000, .base_va = 0x2000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x2000, .base_va = 0x1000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x3000, .base_va = 0x1000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE }
	};

	test_helpers_expect_assert_fail(true);
	sort_mmap_region_array(dup_regions, 3);
	test_helpers_fail_if_no_assert_failed();
}

/*
 * Test: sort_mmap_region_array with overlapping regions triggers assertion
 */
ASSERT_TEST(xlat_low_va, sort_overlapping_regions_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that sort_mmap_region_array asserts when overlapping
	 * regions are detected in the array.
	 ******************************************************************/

	struct xlat_mmap_region overlap_regions[3] = {
		{ .base_pa = 0x1000, .base_va = 0x1000, .size = SZ_16K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x2000, .base_va = 0x2000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x6000, .base_va = 0x6000, .size = SZ_4K, .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE }
	};

	test_helpers_expect_assert_fail(true);
	sort_mmap_region_array(overlap_regions, 3);
	test_helpers_fail_if_no_assert_failed();
}

/*
 * Test: find_va_pool_base with empty region array
 */
TEST(xlat_low_va, find_va_pool_base_empty_regions_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that find_va_pool_base() returns a valid base address
	 * when given an empty region array (0 regions).
	 * Should return minimum address (SZ_1G) + alignment + gap.
	 ******************************************************************/

	struct xlat_mmap_region empty_regions[1];
	uintptr_t l1_block_size = XLAT_BLOCK_SIZE(1);
	uintptr_t min_address = SZ_1G;

	uintptr_t va_pool_base = find_va_pool_base(empty_regions, 0);

	/* Should be at least min_address + gap */
	CHECK_TRUE(va_pool_base >= (min_address + l1_block_size));
	/* Should be aligned to L1 block size */
	CHECK_TRUE(ALIGNED(va_pool_base, l1_block_size));
}

/*
 * Test: find_va_pool_base with single region
 */
TEST(xlat_low_va, find_va_pool_base_single_region_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that find_va_pool_base() correctly places the VA pool
	 * after a single region with proper alignment and gap.
	 ******************************************************************/

	struct xlat_mmap_region regions[1] = {
		{ .base_pa = 0x1000, .base_va = SZ_1G, .size = SZ_1G,
		  .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE }
	};
	uintptr_t l1_block_size = XLAT_BLOCK_SIZE(1);
	uintptr_t region_end = SZ_1G + SZ_1G;

	uintptr_t va_pool_base = find_va_pool_base(regions, 1);

	/* Should be after the region */
	CHECK_TRUE(va_pool_base > region_end);
	/* Should be aligned to L1 block size */
	CHECK_TRUE(ALIGNED(va_pool_base, l1_block_size));
	/* Should have gap of at least 1 L1 block from region */
	CHECK_TRUE((va_pool_base - region_end) >= l1_block_size);
	/* Gap should be a multiple of L1 block size */
	CHECK_TRUE(((va_pool_base - region_end) % l1_block_size) == 0U);
}

/*
 * Test: find_va_pool_base with multiple regions
 */
TEST(xlat_low_va, find_va_pool_base_multiple_regions_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that find_va_pool_base() finds the highest region end
	 * and places the pool after it with proper alignment.
	 ******************************************************************/

	struct xlat_mmap_region regions[3] = {
		{ .base_pa = 0x1000, .base_va = SZ_1G, .size = SZ_1G,
		  .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x2000, .base_va = SZ_1G + SZ_2G, .size = SZ_2G,
		  .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE },
		{ .base_pa = 0x3000, .base_va = SZ_1G + SZ_1G, .size = SZ_1G,
		  .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE }
	};
	uintptr_t l1_block_size = XLAT_BLOCK_SIZE(1);
	uintptr_t highest_end = SZ_1G + SZ_2G + SZ_2G; /* Region 2 has highest end */

	uintptr_t va_pool_base = find_va_pool_base(regions, 3);

	/* Should be after the highest region */
	CHECK_TRUE(va_pool_base > highest_end);
	/* Should be aligned to L1 block size */
	CHECK_TRUE(ALIGNED(va_pool_base, l1_block_size));
	/* Should have gap of at least 1 L1 block from highest region */
	CHECK_TRUE((va_pool_base - highest_end) >= l1_block_size);
	/* Gap should be a multiple of L1 block size */
	CHECK_TRUE(((va_pool_base - highest_end) % l1_block_size) == 0U);
}

/*
 * Test: find_va_pool_base with region already at L1 block boundary
 */
TEST(xlat_low_va, find_va_pool_base_aligned_region_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that find_va_pool_base() handles regions that are
	 * already aligned to L1 block boundaries correctly.
	 ******************************************************************/

	uintptr_t l1_block_size = XLAT_BLOCK_SIZE(1);
	struct xlat_mmap_region regions[1] = {
		{ .base_pa = 0x1000, .base_va = SZ_2G, .size = l1_block_size,
		  .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE }
	};
	uintptr_t region_end = SZ_2G + l1_block_size;

	uintptr_t va_pool_base = find_va_pool_base(regions, 1);

	/* Should be after the region */
	CHECK_TRUE(va_pool_base > region_end);
	/* Should be aligned to L1 block size */
	CHECK_TRUE(ALIGNED(va_pool_base, l1_block_size));
	/* Should have gap of at least 1 L1 block from region */
	CHECK_TRUE((va_pool_base - region_end) >= l1_block_size);
	/* Gap should be a multiple of L1 block size */
	CHECK_TRUE(((va_pool_base - region_end) % l1_block_size) == 0U);
}

/*
 * Test: find_va_pool_base ensures pool fits within single L1 table
 */
TEST(xlat_low_va, find_va_pool_base_l1_table_boundary_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that find_va_pool_base() moves to the next L1 table
	 * when the pool doesn't fit within the current L1 table.
	 ******************************************************************/

	uintptr_t l1_block_size = XLAT_BLOCK_SIZE(1);
	uintptr_t l1_table_size = l1_block_size * XLAT_TABLE_ENTRIES;

	/* Place region near the end of an L1 table */
	uintptr_t region_va = l1_table_size - (2UL * l1_block_size);
	struct xlat_mmap_region regions[1] = {
		{ .base_pa = 0x1000, .base_va = region_va, .size = SZ_1G,
		  .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE }
	};

	uintptr_t va_pool_base = find_va_pool_base(regions, 1);

	/* Calculate which L1 table the pool is in */
	uintptr_t pool_l1_table_start = round_down(va_pool_base, l1_table_size);
	uintptr_t pool_l1_table_end = pool_l1_table_start + l1_table_size;

	/* Calculate which L1 table the region is in */
	uintptr_t region_l1_table_start = round_down(region_va, l1_table_size);
	uintptr_t region_end = region_va + SZ_1G;

	/* Pool should be in a different L1 table than the region */
	CHECK_TRUE(pool_l1_table_start != region_l1_table_start);

	/* Should have gap of at least 1 L1 block from region */
	CHECK_TRUE((va_pool_base - region_end) >= l1_block_size);

	/* Pool should fit entirely within one L1 table */
	CHECK_TRUE((va_pool_base + RMM_VA_POOL_SIZE) <= pool_l1_table_end);
	/* Should be aligned to L1 block size */
	CHECK_TRUE(ALIGNED(va_pool_base, l1_block_size));
}

/*
 * Test: find_va_pool_base with regions spanning multiple L1 tables
 */
TEST(xlat_low_va, find_va_pool_base_cross_l1_table_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that find_va_pool_base() correctly handles regions
	 * spanning multiple L1 tables and places the pool appropriately.
	 ******************************************************************/

	uintptr_t l1_block_size = XLAT_BLOCK_SIZE(1);
	uintptr_t l1_table_size = l1_block_size * XLAT_TABLE_ENTRIES;

	/* Create a large region that spans multiple L1 tables */
	struct xlat_mmap_region regions[1] = {
		{ .base_pa = 0x1000, .base_va = SZ_1G, .size = l1_table_size * 2,
		  .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE }
	};
	uintptr_t region_end = SZ_1G + (l1_table_size * 2);

	uintptr_t va_pool_base = find_va_pool_base(regions, 1);

	/* Should be after the region */
	CHECK_TRUE(va_pool_base > region_end);
	/* Should be aligned to L1 block size */
	CHECK_TRUE(ALIGNED(va_pool_base, l1_block_size));
	/* Should have at least 1 L1 block gap */
	CHECK_TRUE((va_pool_base - region_end) >= l1_block_size);
	/* Gap should be a multiple of L1 block size */
	CHECK_TRUE(((va_pool_base - region_end) % l1_block_size) == 0U);

	/* Pool should fit entirely within one L1 table */
	uintptr_t pool_l1_table_start = round_down(va_pool_base, l1_table_size);
	uintptr_t pool_l1_table_end = pool_l1_table_start + l1_table_size;
	CHECK_TRUE((va_pool_base + RMM_VA_POOL_SIZE) <= pool_l1_table_end);
}

/*
 * Test: find_va_pool_base with high address regions
 */
TEST(xlat_low_va, find_va_pool_base_high_address_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that find_va_pool_base() correctly handles regions
	 * at very high addresses.
	 ******************************************************************/

	uintptr_t l1_block_size = XLAT_BLOCK_SIZE(1);
	uintptr_t high_va = 0x100000000000UL; /* 16TB */

	struct xlat_mmap_region regions[1] = {
		{ .base_pa = 0x1000, .base_va = high_va, .size = SZ_1G,
		  .attr = MT_RW_DATA | MT_REALM, .granularity = GRANULE_SIZE }
	};
	uintptr_t region_end = high_va + SZ_1G;

	uintptr_t va_pool_base = find_va_pool_base(regions, 1);

	/* Should be after the high region */
	CHECK_TRUE(va_pool_base > region_end);
	/* Should be aligned to L1 block size */
	CHECK_TRUE(ALIGNED(va_pool_base, l1_block_size));
	/* Should have gap from region */
	CHECK_TRUE((va_pool_base - region_end) >= l1_block_size);
	/* Gap should be a multiple of L1 block size */
	CHECK_TRUE(((va_pool_base - region_end) % l1_block_size) == 0U);
}

/*
 * Test: Verify shared buffer region is valid
 */
TEST(xlat_low_va, xlat_low_va_shared_buffer_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that the shared buffer region has a valid VA and size.
	 ******************************************************************/

	uintptr_t shared_buf_va = xlat_low_va_shared_buf_va();
	struct xlat_low_va_info *info = xlat_get_low_va_info();
	bool found_shared = false;

	for (unsigned int i = 0U; i < info->low_va_regions_num; i++) {
		if (info->low_va_regions[i].base_va == shared_buf_va) {
			found_shared = true;
			CHECK_TRUE(info->low_va_regions[i].size > 0UL);
			break;
		}
	}

	CHECK_TRUE(found_shared);
}

/*
 * Test: Verify VA pool size and base is reasonable
 */
TEST(xlat_low_va, xlat_low_va_pool_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that the VA pool has a reasonable minimum size and base.
	 ******************************************************************/

	struct xlat_low_va_info *info = xlat_get_low_va_info();

	/* VA pool size should be at least 1GB and aligned to 1GB */
	CHECK_TRUE(info->dyn_va_pool_size >= XLAT_BLOCK_SIZE(1U));
	CHECK_TRUE(ALIGNED(info->dyn_va_pool_size, XLAT_BLOCK_SIZE(1U)));

	uintptr_t dyn_base = xlat_low_va_get_dyn_va_base();

	CHECK_TRUE(dyn_base == info->dyn_va_pool_base);
	CHECK_TRUE(dyn_base >= XLAT_BLOCK_SIZE(1U));
	/* Should be aligned to L1 block size (1GB) */
	CHECK_TRUE(ALIGNED(dyn_base, XLAT_BLOCK_SIZE(1U)));

}

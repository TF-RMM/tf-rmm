/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_helpers.h>
#include <debug.h>
#include <stdlib.h>
#include <string.h>
#include <utils_def.h>
#include <xlat_defs.h>
#include <xlat_tables.h>	/* API to test */
#include <xlat_test_defs.h>
}

/* L3 table size (2MB with 4KB pages, level 2) */
static const uint64_t L3_TABLE_SIZE = XLAT_BLOCK_SIZE(2);

/*
 * Test group for xlat_estimate_num_l3_l2_tables() function.
 *
 * This function estimates the number of L2 and L3 page tables needed
 * to map given memory regions.
 *
 * Key assumptions from the function comments:
 * 1. Regions are sorted by ascending base_va
 * 2. Regions are aligned to PAGE_SIZE
 * 3. Regions do not overlap
 */
TEST_GROUP(xlat_tests_estimate) {
	TEST_SETUP()
	{
		/* Nothing to do */
	}

	TEST_TEARDOWN()
	{
		/* Nothing to do */
	}
};

/*
 * Test: Empty region array
 * Assumption tested: Function handles zero regions correctly
 */
TEST(xlat_tests_estimate, empty_regions)
{
	unsigned long result;

	result = xlat_estimate_num_l3_l2_tables(NULL, 0U);

	CHECK_EQUAL(0UL, result);
}

/*
 * Test: Single region aligned to L3 table size, requires L3 tables
 * Assumption tested: Single region with small granularity
 */
TEST(xlat_tests_estimate, single_region_small_granularity)
{
	struct xlat_mmap_region regions[1];
	unsigned long result;

	/* Region: 4MB at 0x1000000, requiring PAGE_SIZE granularity */
	regions[0].base_va = 0x1000000UL;
	regions[0].base_pa = 0x2000000UL;
	regions[0].size = 4 * 1024 * 1024UL;  /* 4MB */
	regions[0].granularity = PAGE_SIZE;
	regions[0].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * 4MB = 2 * 2MB L3 blocks
	 * Granularity is PAGE_SIZE (< L3_TABLE_SIZE), so L3 tables needed
	 * Also needs 1 L2 table (region < 1GB)
	 * Total: 2 L3 + 1 L2 = 3
	 */
	CHECK_EQUAL(3UL, result);
}

/*
 * Test: Single region aligned to L3 table size, large granularity
 * Assumption tested: Region with granularity >= L3 table size doesn't need L3 tables
 */
TEST(xlat_tests_estimate, single_region_large_granularity_aligned)
{
	struct xlat_mmap_region regions[1];
	unsigned long result;

	/* Region: 4MB at aligned address, with 2MB granularity */
	regions[0].base_va = 0x1000000UL;  /* Aligned to 2MB */
	regions[0].base_pa = 0x2000000UL;  /* Aligned to 2MB */
	regions[0].size = 4 * 1024 * 1024UL;  /* 4MB */
	regions[0].granularity = L3_TABLE_SIZE;  /* 2MB granularity */
	regions[0].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * Region is aligned to 2MB and granularity equals L3_TABLE_SIZE
	 * No L3 tables needed (can use 2MB block descriptors)
	 * But still needs 1 L2 table (granularity 2MB < 1GB)
	 * Total: 0 L3 + 1 L2 = 1
	 */
	CHECK_EQUAL(1UL, result);

	/* Additional check: Same region but with unaligned PA */
	regions[0].base_va = 0x1000000UL;  /* Aligned to 2MB */
	regions[0].base_pa = 0x2001000UL;  /* NOT aligned to 2MB */
	regions[0].size = 4 * 1024 * 1024UL;  /* 4MB */
	regions[0].granularity = L3_TABLE_SIZE;  /* 2MB granularity */
	regions[0].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * VA aligned but PA unaligned for non-transient region
	 * L3 tables needed despite large granularity
	 * Total: 2 L3 + 1 L2 = 3
	 */
	CHECK_EQUAL(3UL, result);
}

/*
 * Test: Single region NOT aligned to L3 table size
 * Assumption tested: Unaligned regions require tables
 */
TEST(xlat_tests_estimate, single_region_unaligned_va)
{
	struct xlat_mmap_region regions[1];
	unsigned long result;

	/* Region: 2MB at unaligned address */
	regions[0].base_va = 0x1001000UL;  /* Not aligned to 2MB */
	regions[0].base_pa = 0x2000000UL;  /* Aligned */
	regions[0].size = 2 * 1024 * 1024UL;  /* 2MB */
	regions[0].granularity = L3_TABLE_SIZE;
	regions[0].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * VA is not aligned to L3_TABLE_SIZE, so L3 table is needed
	 * Covers 2 L3 blocks (round_down to round_up)
	 * Also needs 1 L2 table
	 * Total: 2 L3 + 1 L2 = 3
	 */
	CHECK_EQUAL(3UL, result);
}

/*
 * Test: Single region with unaligned PA (non-transient)
 * Assumption tested: PA alignment matters for non-transient regions
 */
TEST(xlat_tests_estimate, single_region_unaligned_pa)
{
	struct xlat_mmap_region regions[1];
	unsigned long result;

	/* Region: 2MB at aligned VA but unaligned PA */
	regions[0].base_va = 0x1000000UL;  /* Aligned to 2MB */
	regions[0].base_pa = 0x2001000UL;  /* Not aligned to 2MB */
	regions[0].size = 2 * 1024 * 1024UL;  /* 2MB */
	regions[0].granularity = L3_TABLE_SIZE;
	regions[0].attr = MT_DEVICE;  /* Non-transient */

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * PA is not aligned for non-transient region, L3 table needed
	 * Total: 1 L3 + 1 L2 = 2
	 */
	CHECK_EQUAL(2UL, result);
}

/*
 * Test: Single transient region with unaligned PA
 * Assumption tested: PA alignment doesn't matter for transient regions
 */
TEST(xlat_tests_estimate, single_region_transient_unaligned_pa)
{
	struct xlat_mmap_region regions[1];
	unsigned long result;

	/* Transient region: aligned VA, unaligned PA is OK */
	regions[0].base_va = 0x1000000UL;  /* Aligned to 2MB */
	regions[0].base_pa = 0x0UL;  /* Transient, PA doesn't matter */
	regions[0].size = 2 * 1024 * 1024UL;  /* 2MB */
	regions[0].granularity = L3_TABLE_SIZE;
	regions[0].attr = MT_TRANSIENT;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * Transient region with proper VA alignment and size for L3
	 * No L3 tables needed, but still needs 1 L2 table (granularity 2MB < 1GB)
	 * Total: 0 L3 + 1 L2 = 1
	 */
	CHECK_EQUAL(1UL, result);
}

/*
 * Test: Single region with unaligned end address
 * Assumption tested: End alignment affects table count
 */
TEST(xlat_tests_estimate, single_region_unaligned_end)
{
	struct xlat_mmap_region regions[1];
	unsigned long result;

	/* Region: aligned start but unaligned end */
	regions[0].base_va = 0x1000000UL;  /* Aligned to 2MB */
	regions[0].base_pa = 0x2000000UL;  /* Aligned to 2MB */
	regions[0].size = 3 * 1024 * 1024UL;  /* 3MB - not aligned to 2MB */
	regions[0].granularity = L3_TABLE_SIZE;
	regions[0].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * End address not aligned, L3 table needed
	 * round_up(3MB, 2MB) = 4MB = 2 L3 tables
	 * Total: 2 L3 + 1 L2 = 3
	 */
	CHECK_EQUAL(3UL, result);

	/* Additional check: Unaligned end AND unaligned PA */
	regions[0].base_va = 0x1000000UL;  /* Aligned to 2MB */
	regions[0].base_pa = 0x2001000UL;  /* NOT aligned to 2MB */
	regions[0].size = 3 * 1024 * 1024UL;  /* 3MB - not aligned to 2MB */
	regions[0].granularity = L3_TABLE_SIZE;
	regions[0].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * Both end address and PA unaligned
	 * L3 tables still needed
	 * Total: 2 L3 + 1 L2 = 3
	 */
	CHECK_EQUAL(3UL, result);
}

/*
 * Test: Multiple adjacent regions sharing L3 table space
 * Assumption tested: Regions sorted by VA, adjacent regions share tables
 */
TEST(xlat_tests_estimate, multiple_adjacent_regions)
{
	struct xlat_mmap_region regions[2];
	unsigned long result;

	/* First region: 1MB at 0x1000000 */
	regions[0].base_va = 0x1000000UL;
	regions[0].base_pa = 0x2000000UL;
	regions[0].size = 1 * 1024 * 1024UL;  /* 1MB */
	regions[0].granularity = PAGE_SIZE;
	regions[0].attr = MT_DEVICE;

	/* Second region: 1MB at 0x1100000 (adjacent) */
	regions[1].base_va = 0x1100000UL;
	regions[1].base_pa = 0x2100000UL;
	regions[1].size = 1 * 1024 * 1024UL;  /* 1MB */
	regions[1].granularity = PAGE_SIZE;
	regions[1].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 2U);

	/*
	 * Both regions fit in the same 2MB L3 table
	 * Only 1 L3 table needed
	 * Total: 1 L3 + 1 L2 = 2
	 */
	CHECK_EQUAL(2UL, result);

	/* Additional check: Same regions but with unaligned PAs */
	regions[0].base_va = 0x1000000UL;
	regions[0].base_pa = 0x2001000UL;  /* Unaligned PA */
	regions[0].size = 1 * 1024 * 1024UL;  /* 1MB */
	regions[0].granularity = PAGE_SIZE;
	regions[0].attr = MT_DEVICE;

	regions[1].base_va = 0x1100000UL;
	regions[1].base_pa = 0x2101000UL;  /* Unaligned PA */
	regions[1].size = 1 * 1024 * 1024UL;  /* 1MB */
	regions[1].granularity = PAGE_SIZE;
	regions[1].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 2U);

	/*
	 * PA alignment doesn't affect result with PAGE_SIZE granularity
	 * Both regions still fit in the same 2MB L3 table
	 * Total: 1 L3 + 1 L2 = 2
	 */
	CHECK_EQUAL(2UL, result);
}

/*
 * Test: Multiple adjacent regions, one of them needs L3 table and other does not.
 * Assumption tested: Mixed requirements for adjacent regions.
 */
TEST(xlat_tests_estimate, multiple_adjacent_mixed_granularity)
{
	struct xlat_mmap_region regions[2];
	unsigned long result;

	/* First region: 2MB at 0x10000000 with large granularity (no L3 needed) */
	regions[0].base_va = 0x10000000UL;
	regions[0].base_pa = 0x20000000UL;
	regions[0].size = 2 * 1024 * 1024UL;  /* 2MB */
	regions[0].granularity = L3_TABLE_SIZE;  /* 2MB granularity */
	regions[0].attr = MT_DEVICE;

	/* Second region: 2MB at 0x10200000 (adjacent) with small granularity (L3 needed) */
	regions[1].base_va = 0x10200000UL;
	regions[1].base_pa = 0x20200000UL;
	regions[1].size = 2 * 1024 * 1024UL;  /* 2MB */
	regions[1].granularity = PAGE_SIZE;
	regions[1].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 2U);

	/*
	 * Region 0: No L3 tables needed (2MB aligned with 2MB granularity)
	 * Region 1: 1 L3 table needed (PAGE_SIZE granularity)
	 * Both regions share the same L2 table (within same 1GB range)
	 * Total: 1 L3 + 1 L2 = 2
	 */
	CHECK_EQUAL(2UL, result);

	/* Additional check: First region with large granularity but PA is unaligned (L3 needed) */
	regions[0].base_va = 0x10000000UL;
	regions[0].base_pa = 0x20001000UL;  /* Unaligned PA */
	regions[0].size = 2 * 1024 * 1024UL;  /* 2MB */
	regions[0].granularity = L3_TABLE_SIZE;  /* 2MB granularity */
	regions[0].attr = MT_DEVICE;  /* Non-transient, so PA alignment matters */

	/* Use the same second region */
	result = xlat_estimate_num_l3_l2_tables(regions, 2U);

	/*
	 * Region 0: 1 L3 table needed (large granularity but PA unaligned for non-transient)
	 * Region 1: 1 L3 table needed (PAGE_SIZE granularity)
	 * Both regions share the same L2 table (within same 1GB range)
	 * Total: 2 L3 + 1 L2 = 3
	 */
	CHECK_EQUAL(3UL, result);
}

/*
 * Test: Multiple non-adjacent regions
 * Assumption tested: Non-overlapping regions sorted by VA
 */
TEST(xlat_tests_estimate, multiple_nonadjacent_regions)
{
	struct xlat_mmap_region regions[2];
	unsigned long result;

	/* First region: 2MB at 0x1000000 */
	regions[0].base_va = 0x1000000UL;
	regions[0].base_pa = 0x2000000UL;
	regions[0].size = 2 * 1024 * 1024UL;
	regions[0].granularity = PAGE_SIZE;
	regions[0].attr = MT_DEVICE;

	/* Second region: 2MB at 0x10000000 (far away) */
	regions[1].base_va = 0x10000000UL;
	regions[1].base_pa = 0x20000000UL;
	regions[1].size = 2 * 1024 * 1024UL;
	regions[1].granularity = PAGE_SIZE;
	regions[1].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 2U);

	/*
	 * Two separate regions, each needing 1 L3 table
	 * Total: 2 L3 + 1 L2 = 3
	 */
	CHECK_EQUAL(3UL, result);
}

/*
 * Test: Region requiring L2 tables (small granularity, large size)
 * Assumption tested: L2 table estimation for regions needing finer granularity
 */
TEST(xlat_tests_estimate, region_requiring_l2_tables)
{
	struct xlat_mmap_region regions[1];
	unsigned long result;

	/* Large region with small granularity */
	regions[0].base_va = 0x1000000UL;
	regions[0].base_pa = 0x2000000UL;
	regions[0].size = 2UL * 1024 * 1024 * 1024;  /* 2GB */
	regions[0].granularity = PAGE_SIZE;  /* Small granularity */
	regions[0].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * 2GB region starting at 0x1000000 (16MB offset)
	 * Small granularity requires both L2 and L3 tables
	 * L2 range: round_down(0x1000000, 1GB) to round_up(0x81000000, 1GB)
	 *         = 0x0 to 0xC0000000 (3GB) = 3 L2 tables
	 * L3 tables: 2GB / 2MB = 1024
	 * Total: 1024 L3 + 3 L2 = 1027
	 */
	CHECK_EQUAL(1027UL, result);

	/* Additional check: Same region with unaligned PA */
	regions[0].base_va = 0x1000000UL;
	regions[0].base_pa = 0x2001000UL;  /* Unaligned PA */
	regions[0].size = 2UL * 1024 * 1024 * 1024;  /* 2GB */
	regions[0].granularity = PAGE_SIZE;  /* Small granularity */
	regions[0].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * PA unaligned but PAGE_SIZE granularity already requires L3 tables
	 * Result unchanged: 1024 L3 + 3 L2 = 1027
	 */
	CHECK_EQUAL(1027UL, result);

	/* Large region with L3_TABLE_SIZE granularity */
	regions[0].base_va = 0x1000000UL;
	regions[0].base_pa = 0x2000000UL;
	regions[0].size = 2UL * 1024 * 1024 * 1024;  /* 2GB */
	regions[0].granularity = L3_TABLE_SIZE;  /* Large granularity */
	regions[0].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * 2GB region starting at 0x1000000 (16MB offset)
	 * Region is aligned to 2MB with 2MB granularity
	 * No L3 tables needed (can use 2MB block descriptors)
	 * L2 range: round_down(0x1000000, 1GB) to round_up(0x81000000, 1GB)
	 *         = 0x0 to 0xC0000000 (3GB) = 3 L2 tables
	 * Total: 0 L3 + 3 L2 = 3
	 */
	CHECK_EQUAL(3UL, result);
}

/*
 * Test: Multiple regions with mixed granularities
 * Assumption tested: Different regions can have different requirements
 */
TEST(xlat_tests_estimate, mixed_granularity_regions)
{
	struct xlat_mmap_region regions[3];
	unsigned long result;

	/* First: PAGE_SIZE granularity */
	regions[0].base_va = 0x1000000UL;
	regions[0].base_pa = 0x2000000UL;
	regions[0].size = 2 * 1024 * 1024UL; /* 2MB */
	regions[0].granularity = PAGE_SIZE;
	regions[0].attr = MT_DEVICE;

	/* Second: L3_TABLE_SIZE granularity, aligned */
	regions[1].base_va = 0x10000000UL;
	regions[1].base_pa = 0x20000000UL;
	regions[1].size = 2 * 1024 * 1024UL; /* 2MB */
	regions[1].granularity = L3_TABLE_SIZE;
	regions[1].attr = MT_DEVICE;

	/* Third: PAGE_SIZE granularity */
	regions[2].base_va = 0x20000000UL;
	regions[2].base_pa = 0x30000000UL;
	regions[2].size = 4 * 1024 * 1024UL; /* 4MB */
	regions[2].granularity = PAGE_SIZE;
	regions[2].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 3U);

	/*
	 * Region 0: 1 L3 table (+ 1 L2)
	 * Region 1: 0 L3 tables (aligned, large granularity, shares L2)
	 * Region 2: 2 L3 tables (shares L2)
	 * Total: 3 L3 + 1 L2 = 4
	 */
	CHECK_EQUAL(4UL, result);

	/* Additional check: Region 1 with unaligned PA */
	regions[0].base_va = 0x1000000UL;
	regions[0].base_pa = 0x2000000UL;
	regions[0].size = 2 * 1024 * 1024UL; /* 2MB */
	regions[0].granularity = PAGE_SIZE;
	regions[0].attr = MT_DEVICE;

	regions[1].base_va = 0x10000000UL;
	regions[1].base_pa = 0x20001000UL;  /* Unaligned PA */
	regions[1].size = 2 * 1024 * 1024UL; /* 2MB */
	regions[1].granularity = L3_TABLE_SIZE;
	regions[1].attr = MT_DEVICE;

	regions[2].base_va = 0x20000000UL;
	regions[2].base_pa = 0x30000000UL;
	regions[2].size = 4 * 1024 * 1024UL; /* 4MB */
	regions[2].granularity = PAGE_SIZE;
	regions[2].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 3U);

	/*
	 * Region 0: 1 L3 table
	 * Region 1: 1 L3 table (PA unaligned, needs L3 despite large granularity)
	 * Region 2: 2 L3 tables
	 * Total: 4 L3 + 1 L2 = 5
	 */
	CHECK_EQUAL(5UL, result);
}

/*
 * Test: Region spanning multiple L2 and L3 boundaries
 * Assumption tested: Large regions correctly counted
 */
TEST(xlat_tests_estimate, large_region_multiple_boundaries)
{
	struct xlat_mmap_region regions[1];
	unsigned long result;

	/* Very large region: 4GB */
	regions[0].base_va = 0x0UL;
	regions[0].base_pa = 0x0UL;
	regions[0].size = 4UL * 1024 * 1024 * 1024;  /* 4GB */
	regions[0].granularity = PAGE_SIZE;
	regions[0].attr = MT_MEMORY;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * 4GB region with PAGE_SIZE granularity
	 * L2 tables: 4GB / 1GB = 4
	 * L3 tables: 4GB / 2MB = 2048
	 * Total: 2052
	 */
	CHECK_EQUAL(2052UL, result);
}

/*
 * Test: Regions within same L3 block but not adjacent
 * Assumption tested: Overlapping L3 table coverage
 */
TEST(xlat_tests_estimate, regions_same_l3_block)
{
	struct xlat_mmap_region regions[2];
	unsigned long result;

	/* Both regions in same 2MB L3 block */
	regions[0].base_va = 0x1000000UL;  /* Start of 2MB block */
	regions[0].base_pa = 0x2000000UL;
	regions[0].size = 512 * 1024UL;  /* 512KB */
	regions[0].granularity = PAGE_SIZE;
	regions[0].attr = MT_DEVICE;

	regions[1].base_va = 0x1100000UL;  /* Still in same 2MB block */
	regions[1].base_pa = 0x2100000UL;
	regions[1].size = 512 * 1024UL;  /* 512KB */
	regions[1].granularity = PAGE_SIZE;
	regions[1].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 2U);

	/*
	 * Both regions share the same 2MB L3 block
	 * Only 1 L3 table needed
	 * Total: 1 L3 + 1 L2 = 2
	 */
	CHECK_EQUAL(2UL, result);
}

/*
 * Test: Region crossing L3 boundary
 * Assumption tested: Regions spanning multiple L3 blocks
 */
TEST(xlat_tests_estimate, region_crossing_l3_boundary)
{
	struct xlat_mmap_region regions[1];
	unsigned long result;

	/* Region crossing 2MB boundary */
	regions[0].base_va = 0x1F00000UL;  /* 1MB before 2MB boundary */
	regions[0].base_pa = 0x2F00000UL;
	regions[0].size = 2 * 1024 * 1024UL;  /* 2MB, crosses boundary */
	regions[0].granularity = PAGE_SIZE;
	regions[0].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * Region spans from 0x1F00000 to 0x2F00000
	 * 2MB = 0x200000
	 * Start: 0x1F00000
	 * End: 0x1F00000 + 0x200000 = 0x2100000
	 * round_down(0x1F00000, 0x200000) = 0x1E00000
	 * round_up(0x2100000, 0x200000) = 0x2200000
	 * Difference: 0x2200000 - 0x1E00000 = 0x400000 = 4MB = 2 L3 tables
	 * Total: 2 L3 + 1 L2 = 3
	 */
	CHECK_EQUAL(3UL, result);
}

/*
 * Test: Minimum size region (PAGE_SIZE)
 * Assumption tested: PAGE_SIZE aligned regions (minimum alignment)
 */
TEST(xlat_tests_estimate, minimum_size_region)
{
	struct xlat_mmap_region regions[1];
	unsigned long result;

	/* Single page */
	regions[0].base_va = 0x1000000UL;
	regions[0].base_pa = 0x2000000UL;
	regions[0].size = PAGE_SIZE;
	regions[0].granularity = PAGE_SIZE;
	regions[0].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * Single page in a 2MB L3 block
	 * Needs 1 L3 table
	 * Total: 1 L3 + 1 L2 = 2
	 */
	CHECK_EQUAL(2UL, result);
}

/*
 * Test: Multiple regions in sorted order
 * Assumption tested: Regions sorted by ascending base_va
 */
TEST(xlat_tests_estimate, multiple_sorted_regions)
{
	struct xlat_mmap_region regions[4];
	unsigned long result;

	/* Region at 0x1000000 */
	regions[0].base_va = 0x1000000UL;
	regions[0].base_pa = 0x2000000UL;
	regions[0].size = 2 * 1024 * 1024UL;
	regions[0].granularity = PAGE_SIZE;
	regions[0].attr = MT_DEVICE;

	/* Region at 0x5000000 */
	regions[1].base_va = 0x5000000UL;
	regions[1].base_pa = 0x6000000UL;
	regions[1].size = 2 * 1024 * 1024UL;
	regions[1].granularity = PAGE_SIZE;
	regions[1].attr = MT_DEVICE;

	/* Region at 0x10000000 */
	regions[2].base_va = 0x10000000UL;
	regions[2].base_pa = 0x20000000UL;
	regions[2].size = 2 * 1024 * 1024UL;
	regions[2].granularity = PAGE_SIZE;
	regions[2].attr = MT_DEVICE;

	/* Region at 0x20000000 */
	regions[3].base_va = 0x20000000UL;
	regions[3].base_pa = 0x30000000UL;
	regions[3].size = 2 * 1024 * 1024UL;
	regions[3].granularity = PAGE_SIZE;
	regions[3].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 4U);

	/*
	 * 4 separate regions, each 2MB aligned and sized
	 * Each needs 1 L3 table
	 * Total: 4 L3 + 1 L2 = 5
	 */
	CHECK_EQUAL(5UL, result);
}

/*
 * Test: Region requiring only L2 table (aligned to L3 but not L2)
 * Assumption tested: L2 table needed when granularity < L2_TABLE_SIZE but region
 *                    is aligned to L3_TABLE_SIZE
 */
TEST(xlat_tests_estimate, region_needing_l2_only)
{
	struct xlat_mmap_region regions[1];
	unsigned long result;

	/* 1GB region aligned to 2MB but not 1GB */
	regions[0].base_va = 0x80000000UL;  /* Aligned to 2MB but crossing 1GB */
	regions[0].base_pa = 0x80000000UL;
	regions[0].size = 1UL * 1024 * 1024 * 1024;  /* 1GB */
	regions[0].granularity = L3_TABLE_SIZE;  /* 2MB granularity */
	regions[0].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * 1GB region at 0x80000000 (2GB) with 2MB granularity
	 * 0x80000000 is aligned to 1GB (2 * 1GB)
	 * No L3 tables needed (aligned, granularity 2MB)
	 * L2: granularity 2MB < 1GB, so needs L2 table
	 * round_down(0x80000000, 1GB) = 0x80000000
	 * round_up(0xC0000000, 1GB) = 0xC0000000
	 * (0xC0000000 - 0x80000000) / 1GB = 1 L2 table
	 * Total: 0 L3 + 1 L2 = 1
	 */
	CHECK_EQUAL(1UL, result);
}

/*
 * Test: Region requiring no L2 table (aligned to L1 block)
 * Assumption tested: L2 table is not needed when granularity >= L2_TABLE_SIZE and region
 *                    is aligned to L2_TABLE_SIZE
 */
TEST(xlat_tests_estimate, region_needing_no_l2_table)
{
	struct xlat_mmap_region regions[1];
	unsigned long result;

	/* 1GB region with 1GB granularity, fully aligned */
	regions[0].base_va = 0x40000000UL;  /* 1GB - aligned */
	regions[0].base_pa = 0x40000000UL;  /* 1GB - aligned */
	regions[0].size = 1UL * 1024 * 1024 * 1024;  /* 1GB */
	regions[0].granularity = XLAT_BLOCK_SIZE(1);  /* 1GB granularity */
	regions[0].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * 1GB region at 0x40000000 with 1GB granularity
	 * Base and end are aligned to 1GB boundaries
	 * No L3 tables needed (granularity 1GB >= 2MB)
	 * No L2 tables needed (granularity 1GB >= 1GB, aligned)
	 * Total: 0
	 */
	CHECK_EQUAL(0UL, result);

	/* Additional check: Same region but with PA aligned to 4KB */
	regions[0].base_va = 0x40000000UL;  /* 1GB - aligned */
	regions[0].base_pa = 0x40001000UL;  /* PA aligned to 4KB */
	regions[0].size = 1UL * 1024 * 1024 * 1024;  /* 1GB */
	regions[0].granularity = XLAT_BLOCK_SIZE(1);  /* 1GB granularity */
	regions[0].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * 1GB region with 1GB granularity but PA aligned to 4KB.
	 * L3 tables needed and L2 tables needed
	 * Total: 512 L3 + 1 L2 = 513
	 */
	CHECK_EQUAL(513UL, result);

	/* Additional check: Same region but with PA aligned to 2MB */
	regions[0].base_va = 0x40000000UL;  /* 1GB - aligned */
	regions[0].base_pa = 0x40200000UL;  /* PA aligned to 2MB */
	regions[0].size = 1UL * 1024 * 1024 * 1024;  /* 1GB */
	regions[0].granularity = XLAT_BLOCK_SIZE(1);  /* 1GB granularity */
	regions[0].attr = MT_DEVICE;

	result = xlat_estimate_num_l3_l2_tables(regions, 1U);

	/*
	 * 1GB region with 1GB granularity but PA aligned to 2MB.
	 * 1 L2 table needed
	 */
	CHECK_EQUAL(1UL, result);
}

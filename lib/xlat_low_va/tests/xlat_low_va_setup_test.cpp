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
}

#define MAX_RAND_BLOCKS_NUM \
	(XLAT_LOW_VIRT_ADDR_SPACE_SIZE / XLAT_BLOCK_SIZE(0))

static struct xlat_low_va_info saved_low_va_info;

/*
 * Helper function to collect and validate static regions from low_va_info
 * Returns the count of static regions found
 */
static unsigned int collect_and_validate_static_regions(
	struct xlat_low_va_info *info,
	struct xlat_mmap_region **static_regions)
{
	unsigned int static_region_count = 0U;
	int ret;
	uint64_t *table_ptr;
	int level;
	unsigned int index;

	/* Collect all actual regions from low_va_regions array (skip terminators and dynamic VA pool) */
	for (unsigned int i = 0U; i < TOTAL_MMAP_REGIONS; i++) {
		if (info->low_va_regions[i].base_va != 0UL &&
		    info->low_va_regions[i].base_va != info->dyn_va_pool_base) {
			static_regions[static_region_count] = &info->low_va_regions[i];
			static_region_count++;
		}
	}

	CHECK_TRUE(static_region_count >= 2U);

	/* Validate that all regions are mapped in the translation tables */
	for (unsigned int i = 0U; i < static_region_count; i++) {
		CHECK_TRUE(static_regions[i] != NULL);
		CHECK_TRUE(static_regions[i]->size > 0UL);

		uint64_t tte;
		ret = xlat_test_helpers_table_walk(&info->low_va_ctx, static_regions[i]->base_va,
						   &tte, &table_ptr, &level, &index);
		CHECK_EQUAL(0, ret);
		CHECK_TRUE((tte & DESC_MASK) != INVALID_DESC); /* Valid descriptor */
	}

	return static_region_count;
}

/*
 * Test group for xlat_low_va Live Firmware Activation (LFA) scenarios
 */
TEST_GROUP(xlat_low_va_setup) {
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
 * Test: Live Firmware Activation with preserved dynamic mappings
 */
TEST(xlat_low_va_setup, xlat_low_va_lfa_preserve_dynamic_mappings_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Test Live Firmware Activation (LFA) scenario:
	 * 1. Get the current low_va_info and validate it's populated
	 * 2. Collect and validate initial static mappings from low_va_info
	 * 3. Add dynamic mappings to the dynamic VA pool
	 * 4. Validate dynamic mappings are correctly established in tables
	 * 5. Save current state and create 2 new static regions for LFA
	 * 6. Call xlat_low_va_setup with new regions and previous low_va_info
	 * 7. Validate new setup has all old + new static regions and preserved dynamic mappings
	 ******************************************************************/

	int ret;
	struct xlat_low_va_info *info;
	uint64_t *table_ptr;
	int level;
	unsigned int index;

	/* Step 1: Get the current low_va_info and validate it's populated */
	info = xlat_get_low_va_info();
	CHECK_TRUE(info != NULL);
	CHECK_TRUE(info->low_va_regions_num > 0U);
	CHECK_TRUE(info->dyn_va_pool_base != 0UL);

	/* Step 2: Validate initial static mappings in low_va_info */
	struct xlat_mmap_region *static_regions[TOTAL_MMAP_REGIONS];
	unsigned int static_region_count = collect_and_validate_static_regions(info, static_regions);

	/* Step 3: Add dynamic mappings */
	uintptr_t test_pas[3] = { 0x10000000UL, 0x20000000UL, 0x30000000UL };
	uintptr_t dyn_vas[3];
	uint64_t dyn_ttes[3];

	for (unsigned int i = 0U; i < 3U; i++) {
		dyn_vas[i] = xlat_low_va_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM,
					    test_pas[i], false);
		CHECK_TRUE(dyn_vas[i] != 0UL);
		CHECK_TRUE(dyn_vas[i] >= info->dyn_va_pool_base);
	}

	/* Step 4: Validate dynamic mappings in tables */
	for (unsigned int i = 0U; i < 3U; i++) {
		ret = xlat_test_helpers_table_walk(&info->dyn_va_ctx, dyn_vas[i],
						   &dyn_ttes[i], &table_ptr, &level, &index);
		CHECK_EQUAL(0, ret);
		CHECK_EQUAL(XLAT_TABLE_LEVEL_MAX, level);
		CHECK_TRUE((dyn_ttes[i] & DESC_MASK) == PAGE_DESC);
		CHECK_EQUAL(test_pas[i], xlat_get_oa_from_tte(dyn_ttes[i]));
	}

	/* Save current low_va_info for LFA */
	struct xlat_low_va_info prev_low_va_info;
	memcpy(&prev_low_va_info, info, sizeof(struct xlat_low_va_info));

	/* Step 5: Create 2 additional static regions, same as initial static regions */
	/* Find the highest VA in static_regions[] - use last entry as they are sorted */
	struct xlat_mmap_region *last_region = static_regions[static_region_count - 1];
	uintptr_t highest_va = last_region->base_va + last_region->size;

	struct xlat_mmap_region lfa_static_regions[2];
	for (unsigned int i = 0U; i < 2U; i++) {
		lfa_static_regions[i].base_va = highest_va + GRANULE_SIZE + (i * GRANULE_SIZE);
		lfa_static_regions[i].base_pa = lfa_static_regions[i].base_va;
		lfa_static_regions[i].size = GRANULE_SIZE;
		lfa_static_regions[i].attr = MT_RO_DATA | MT_REALM;
		lfa_static_regions[i].granularity = GRANULE_SIZE;
	}

	/* Disable MMU */
	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);

	/* Step 6: Call xlat_low_va_setup with pointer to previous low_va_info */
	/* Clear the va_info */
	memset(info, 0, sizeof(struct xlat_low_va_info));

	ret = xlat_low_va_setup(lfa_static_regions, 2U, 0U, &prev_low_va_info);
	CHECK_EQUAL(0, ret);

	/* Enable MMU */
	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Step 7: Validate tables have LFA regions and preserved dynamic mappings */
	info = xlat_get_low_va_info();
	CHECK_TRUE(info != NULL);

	/* Validate the static regions */
	unsigned int lfa_static_region_count = collect_and_validate_static_regions(info, static_regions);
	CHECK_TRUE(lfa_static_region_count == static_region_count + 2U);

	/* Validate dynamic mappings are preserved with same VAs */
	uint64_t preserved_ttes[3];

	for (unsigned int i = 0U; i < 3U; i++) {
		ret = xlat_test_helpers_table_walk(&info->dyn_va_ctx, dyn_vas[i],
						   &preserved_ttes[i], &table_ptr, &level, &index);
		CHECK_EQUAL(0, ret);
		CHECK_EQUAL(XLAT_TABLE_LEVEL_MAX, level);
		CHECK_TRUE((preserved_ttes[i] & DESC_MASK) == PAGE_DESC);
		CHECK_EQUAL(test_pas[i], xlat_get_oa_from_tte(preserved_ttes[i]));
		CHECK_EQUAL(dyn_ttes[i], preserved_ttes[i]);
	}

	/* Clean up dynamic mappings */
	for (unsigned int i = 0U; i < 3U; i++) {
		ret = xlat_low_va_unmap(dyn_vas[i], GRANULE_SIZE);
		CHECK_EQUAL(0, ret);
	}
}

/*
 * Test whether xlat_low_va_setup() returns an error when it
 * received an invalid nregions parameter.
 */
TEST(xlat_low_va_setup, xlat_low_va_setup_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that xlat_low_va_setup() returns -1 when called with
	 * nregions greater than TOTAL_MMAP_REGIONS.
	 ******************************************************************/

	struct xlat_mmap_region *plat_regions = NULL;
	unsigned int nregions = TOTAL_MMAP_REGIONS + 1U;
	int ret;

	/* Disable MMU */
	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);

	ret = xlat_low_va_setup(plat_regions, nregions, 0U, NULL);

	CHECK_EQUAL(-ERANGE, ret);
}

/*
 * Test whether xlat_low_va_setup() returns an error when the va_info
 * structure contains an invalid low_va_regions_capacity field.
 */
TEST(xlat_low_va_setup, xlat_low_va_setup_TC3)
{
	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Verify that xlat_low_va_setup() returns -ERANGE when the va_info
	 * structure contains an invalid low_va_regions_capacity field.
	 ******************************************************************/

	struct xlat_low_va_info va_info;
	struct xlat_mmap_region *plat_regions = NULL;
	unsigned int nregions = 0U;
	int ret;

	memset(&va_info, 0, sizeof(va_info));
	/* Disable MMU */
	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);

	ret = xlat_low_va_setup(plat_regions, nregions, 0U, &va_info);

	CHECK_EQUAL(-ERANGE, ret);
}

/*
 * Test: Live Firmware Activation with VA pool mismatch
 */
TEST(xlat_low_va_setup, xlat_low_va_lfa_va_pool_mismatch_TC1)
{
	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Test Live Firmware Activation (LFA) failure scenarios:
	 * Verify that xlat_low_va_dyn_fixup() returns -EINVAL when the
	 * dynamic VA pool configuration in the previous low_va_info does
	 * not match the newly calculated values.
	 *
	 * This tests the failure path in xlat_low_va_dyn_fixup():
	 *   if ((va_info->dyn_va_ctx_cfg.base_va !=
	 *        round_down(g_va_info.dyn_va_pool_base, XLAT_BLOCK_SIZE(0))) ||
	 *       (va_info->dyn_va_pool_size != RMM_VA_POOL_SIZE))
	 *
	 * Sub-tests:
	 * A. VA pool base address mismatch
	 * B. VA pool size mismatch
	 ******************************************************************/

	int ret;
	struct xlat_low_va_info *info;
	struct xlat_low_va_info prev_low_va_info;

	/* Get the current low_va_info and save it */
	info = xlat_get_low_va_info();
	CHECK_TRUE(info != NULL);
	CHECK_TRUE(info->low_va_regions_num > 0U);
	CHECK_TRUE(info->dyn_va_pool_base != 0UL);
	CHECK_TRUE(info->dyn_va_pool_size == RMM_VA_POOL_SIZE);

	/******************************************************************
	 * Sub-test A: VA pool base address mismatch
	 ******************************************************************/

	/* Save current low_va_info */
	memcpy(&prev_low_va_info, info, sizeof(struct xlat_low_va_info));

	/* Intentionally corrupt the VA pool base in prev_low_va_info */
	uintptr_t original_base = prev_low_va_info.dyn_va_ctx_cfg.base_va;
	uintptr_t base_offset = (uintptr_t)((rand() % MAX_RAND_BLOCKS_NUM) + 1U) * XLAT_BLOCK_SIZE(0);
	prev_low_va_info.dyn_va_ctx_cfg.base_va = original_base + base_offset;

	/* Disable MMU */
	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);

	/* Clear the current va_info */
	memset(info, 0, sizeof(struct xlat_low_va_info));

	/* Call xlat_low_va_setup with mismatched base address */
	ret = xlat_low_va_setup(NULL, 0U, 0U, &prev_low_va_info);

	/* Verify it returns -EINVAL due to VA pool base mismatch */
	CHECK_EQUAL(-EINVAL, ret);

	/* Re-enable MMU */
	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);

	/* Restore original state for next sub-test */
	memcpy(info, &saved_low_va_info, sizeof(struct xlat_low_va_info));

	/******************************************************************
	 * Sub-test B: VA pool size mismatch
	 ******************************************************************/

	/* Get fresh info pointer after restore */
	info = xlat_get_low_va_info();

	/* Save current low_va_info again */
	memcpy(&prev_low_va_info, info, sizeof(struct xlat_low_va_info));

	/* Intentionally corrupt the VA pool size in prev_low_va_info */
	uintptr_t size_delta = (uintptr_t)((rand() % MAX_RAND_BLOCKS_NUM) + 1U) * XLAT_BLOCK_SIZE(0);
	if (size_delta >= RMM_VA_POOL_SIZE) {
		size_delta = XLAT_BLOCK_SIZE(0);
	}
	prev_low_va_info.dyn_va_pool_size = RMM_VA_POOL_SIZE - size_delta;

	/* Disable MMU */
	write_sctlr_el2(read_sctlr_el2() & ~SCTLR_ELx_M_BIT);

	/* Clear the current va_info */
	memset(info, 0, sizeof(struct xlat_low_va_info));

	/* Call xlat_low_va_setup with mismatched pool size */
	ret = xlat_low_va_setup(NULL, 0U, 0U, &prev_low_va_info);

	/* Verify it returns -EINVAL due to VA pool size mismatch */
	CHECK_EQUAL(-EINVAL, ret);

	/* Re-enable MMU for teardown */
	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_M_BIT);
}

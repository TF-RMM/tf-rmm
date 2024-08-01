/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_helpers.h>
#include <debug.h>
#include <host_utils.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
#include <xlat_contexts.h>	/* API to test */
#include <xlat_defs.h>
#include <xlat_defs_private.h>
#include <xlat_tables.h>	/* API to test */
#include <xlat_test_defs.h>
#include <xlat_test_helpers.h>
}

/*
 * Generate VA space parameters given a walk start level and a region.
 * The VA returned will fit in a single table of level `level`, so that
 * there translation can start at that given level.
 */
static uint64_t gen_va_space_params_by_lvl(int level,
					   xlat_addr_region_id_t region,
					   size_t *va_size)
{
	assert(level >= XLAT_TEST_MIN_LVL());
	assert(level <= XLAT_TABLE_LEVEL_MAX);
	assert(va_size != NULL);

	*va_size = (1ULL << XLAT_ADDR_SHIFT(level)) *
				XLAT_GET_TABLE_ENTRIES(level);

	return xlat_test_helpers_get_start_va(region, *va_size);
}

/*
 * Generate a mmap array containing a set of mmap regions defined by
 * 'start_va', 'last_lvl' and 'offset'. The mmap array will have
 * three regions:
 *
 *	- First region mapped at the beginning of a table whose final
 *	  lookup level is 'last_lvl'. This region will be descendant of
 *	  an entry at the beginning of a table at level 'first_lvl'.
 *	- Second region mapped at a random index of a table whose final
 *	  lookup level is 'last_lvl'. This region will be descendant of
 *	  an entry at a random index of a table at level 'first_lvl'.
 *	- Third region mapped at the end of a table whose final
 *	  lookup level is 'last_lvl'. This region will be descendant of
 *	  an entry at the final entry of a table at level 'first_lvl'.
 *
 *                                                        ┌──────────┐
 *                                        ┌───────────────┤ First    │
 *                                        │               │ Region   │
 *                                        │               ├──────────┤
 *                                        │               │          │
 *                                        │               │          │
 *                                        │               │          │
 *                                        │               │          │
 *                                        │               │          │
 *                                        │               │          │
 *                                        │               │          │
 *                 ┌──────────────┐       │               │          │
 *                 │              │       │               │          │
 *                 │ First entry  ├───────┘               │          │
 *                 ├──────────────┤                       │          │
 *                 │ Second entry │                       │          │
 *                 │ (Reserved)   │                       └──────────┘
 *                 │              │
 *                 ├──────────────┤
 *                 │              │                        ┌──────────┐
 *                 │              │                        │          │
 *                 │              │                        │          │
 *                 │              │                        │          │
 *                 ├──────────────┤                        ├──────────┤
 *                 │  Second      │                        │ Second   │
 *                 │  Region      ├────────────────────────┤ Region   │
 *                 ├──────────────┤                        ├──────────┤
 *                 │              │                        │          │
 *                 │              │                        │          │
 *                 │              │                        │          │
 *                 │              │                        │          │
 *                 │              │                        │          │
 *                 │              │                        │          │
 *                 ├──────────────┤                        └──────────┘
 *                 │              │
 *                 │ Third Region ├───────┐
 *                 └──────────────┘       │                 ┌─────────┐
 *                   First Level          │                 │         │
 *                                        │                 │         │
 *                                        │                 │         │
 *                                        │                 │         │
 *                                        │                 │         │
 *                                        │                 │         │
 *                                        │                 │         │
 *                                        │                 │         │
 *                                        │                 │         │
 *                                        │                 │         │
 *                                        │                 │         │
 *                                        │                 │         │
 *                                        │                 │         │
 *                                        │                 ├─────────┤
 *                                        └─────────────────┤  Third  |
 *                                                          | region  │
 *                                                          └─────────┘
 *                                                           Last level
 *
 * For all the mmap regions, the granularity (returned in *granularity) is
 * setup to the minimum granularity needed to map a block at level 'last_lvl'.
 * The size of the mmap region is setup to the same as the granularity.
 *
 * This function caters for the reduced number of entries on the
 * tables at level -1.
 *
 * This function also returns :
 *	- An array ('tbl_idxs') with the expected indexes mapping
 *	  the regions at the last level table.
 */
static int gen_mmap_array_by_level(xlat_mmap_region *mmap,
				   unsigned int *tbl_idxs,
				   unsigned int mmap_size,
				   int first_lvl,
				   int last_lvl,
				   size_t *granularity,
				   uint64_t start_va,
				   bool allow_transient)
{
	uint64_t attrs;
	uint64_t mmap_start_va = start_va;
	unsigned int max_table_entries = XLAT_GET_TABLE_ENTRIES(first_lvl);

	assert(mmap_size >= 3U);
	assert(last_lvl > XLAT_TEST_MIN_LVL());
	assert(last_lvl <= XLAT_TABLE_LEVEL_MAX);
	assert(first_lvl >= XLAT_TEST_MIN_LVL());
	assert(first_lvl <= last_lvl);
	assert(mmap != NULL);
	assert(tbl_idxs != NULL);
	assert(granularity != NULL);

	/* Generate a mapping at the beginning of the table */
	tbl_idxs[0U] = 0U;

	/*
	 * Generate a mapping in a random position of the table.
	 * The entry after the first one will always be left intentionally
	 * unused.
	 */
	tbl_idxs[1U] = (unsigned int)test_helpers_get_rand_in_range(2UL,
							max_table_entries - 2);

	/* Generate a mapping at the end of the table */
	tbl_idxs[2U] = max_table_entries - 1U;

	do {
		attrs = xlat_test_helpers_rand_mmap_attrs(true);
	} while ((attrs == MT_TRANSIENT) && (allow_transient == false));

	*granularity = XLAT_BLOCK_SIZE(last_lvl);

	for (unsigned int i = 0U; i < 3U; i++) {
		mmap[i].base_va = mmap_start_va;
		if (first_lvl < last_lvl) {
			/*
			 * Add an offset to the mmap region base VA so that
			 * this region will be mapped to a TTE in the
			 * `first_lvl` table at the same index as specified
			 * in tbl_idxs[].
			 */
			mmap[i].base_va += tbl_idxs[i] *
						XLAT_BLOCK_SIZE(first_lvl);
		}

		mmap[i].base_va += (tbl_idxs[i] * (*granularity));

		/*
		 * PA can be any address (as long as there are not overlaps,
		 * for which there is a specific test). For simplicity,
		 * create an identity mapping using the base_va for the PA.
		 */
		mmap[i].base_pa = mmap[i].base_va & XLAT_TEST_GET_PA_MASK();
		mmap[i].size = *granularity;
		mmap[i].attr = attrs;
		mmap[i].granularity = *granularity;
	}

	return 0;
}

/*
 * Given a context and a set of expected indexes and levels for the last walk,
 * validate that the translation tables in the context are valid.
 * Note that this function expects a valid and initialized context.
 */
static void validate_xlat_tables(xlat_ctx *ctx, unsigned int *expected_idxs,
				 int expected_level)
{
	uint64_t tte, tte_oa, attrs, upper_attrs, lower_attrs, type;
	uint64_t exp_upper_attrs, exp_lower_attrs;
	unsigned int index, granularity, addr_offset;
	uint64_t test_va, pa, pa_mask;
	int level, retval;

	assert(ctx != NULL);
	assert(expected_idxs != NULL);

	for (unsigned int i = 0U; i < ctx->cfg->mmap_regions; i++) {
		granularity = ctx->cfg->mmap[i].granularity;
		addr_offset = (unsigned int)test_helpers_get_rand_in_range(0UL,
							granularity - 1U);
		test_va = ctx->cfg->base_va + ctx->cfg->mmap[i].base_va +
								addr_offset;
		pa = ctx->cfg->mmap[i].base_pa + addr_offset;

		/* Perform a table walk */
		retval = xlat_test_helpers_table_walk(ctx, test_va,
						      &tte, NULL, &level,
						      &index);

		/* Return value */
		CHECK_VERBOSE((retval == 0),
			"Perform table walk for addr 0x%lx", test_va);

		/* Last table level */
		CHECK_EQUAL(expected_level, level);

		/* tte index on the page */
		CHECK_EQUAL(expected_idxs[i], index);

		/* Expected tte attributes */
		retval = xlat_test_helpers_get_attrs_for_va(ctx, test_va,
							     &attrs);

		/* Return value */
		CHECK_EQUAL(0, retval);

		exp_upper_attrs = EXTRACT(UPPER_ATTRS, attrs);
		upper_attrs = EXTRACT(UPPER_ATTRS, tte);
		exp_lower_attrs = EXTRACT(LOWER_ATTRS, attrs);
		if (is_feat_lpa2_4k_present() == true) {
			lower_attrs = EXTRACT(LOWER_ATTRS,
					(tte & ~TTE_OA_BITS_50_51_MASK));
		} else {
			lower_attrs = EXTRACT(LOWER_ATTRS, tte);
		}

		/* Validate that the attributes are as expected */
		CHECK_VERBOSE((exp_upper_attrs == upper_attrs),
			"Validate Upper Attrs: Read 0x%lx - Expected 0x%lx",
				upper_attrs, exp_upper_attrs);

		CHECK_VERBOSE((exp_lower_attrs == lower_attrs),
			"Validate Lower Attrs: Read 0x%lx - Expected 0x%lx",
				lower_attrs, exp_lower_attrs);

		/* Validate the PA */
		pa_mask = (1ULL << XLAT_ADDR_SHIFT(level)) - 1ULL;
		tte_oa = xlat_get_oa_from_tte(tte);

		CHECK_EQUAL(tte_oa, (pa & ~pa_mask));

		/* Validate the descriptor type */
		type = (level == XLAT_TABLE_LEVEL_MAX) ? PAGE_DESC :
							 BLOCK_DESC;
		CHECK_EQUAL(type, (tte & DESC_MASK));
	}
}

void xlat_ctx_init_tc5(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uint64_t start_va;
	size_t va_size, granularity;
	unsigned int mmap_count;
	xlat_addr_region_id_t va_region;
	int retval;
	struct xlat_mmap_region init_mmap[3U];
	unsigned int tbl_idx[3U];
	int base_lvl, end_lvl;

	/**********************************************************************
	 * TEST CASE 5:
	 *
	 * For each possible base level, create a set of mmap regions
	 * ranging from level 1 or 0 (lowest level at which a valid walk can
	 * finish depending on whether FEAT_LPA2 is available) to
	 * XLAT_TABLE_LEVEL_MAX.
	 *
	 * For each possible (va_region, base_lvl, end_lvl) triplet for a
	 * base table there will be three mmap regions created:
	 *
	 *	- First region mapped at the beginning of a table whose final
	 *	  lookup level is 'last_lvl'. This region will be descendant of
	 *	  an entry at the beginning of a 'base_lvl' table.
	 *	- Second region mapped at a random index of a table whose final
	 *	  lookup level is 'last_lvl'. This region will be descendant of
	 *	  an entry at a random index of a 'base_lvl' table.
	 *	- Third region mapped at the end of a table whose final
	 *	  lookup level is 'last_lvl'. This region will be descendant of
	 *	  an entry at the end of a 'base_lvl'.
	 *
	 * Then verify that the tables can be walked and that the levels,
	 * offsets and attributes on the ttes are as expected.
	 *
	 * This test validates that the xlat library is able to create
	 * tables starting on any valid initial lookup level and
	 * finishing on any valid level as well.
	 *********************************************************************/

	mmap_count = 3U;

	end_lvl = XLAT_MIN_BLOCK_LVL();
	for (; end_lvl <= XLAT_TABLE_LEVEL_MAX; end_lvl++) {
		for (int i = 0U; i < VA_REGIONS; i++) {
			va_region = (xlat_addr_region_id_t)i;

			for (base_lvl = XLAT_TEST_MIN_LVL();
			     base_lvl <= end_lvl;
			     base_lvl++) {

				start_va = gen_va_space_params_by_lvl(base_lvl,
								 va_region,
								 &va_size);

				retval = gen_mmap_array_by_level(&init_mmap[0U],
								 &tbl_idx[0U],
								 mmap_count,
								 base_lvl,
								 end_lvl,
								 &granularity,
								 start_va,
								 false);
				/*
				 * verify that the test setup is correct so far
				 */
				CHECK_TRUE(retval == 0);

				/* Clean the data structures */
				memset((void *)&ctx, 0,
						sizeof(struct xlat_ctx));
				memset((void *)&cfg, 0,
						sizeof(struct xlat_ctx_cfg));
				memset((void *)&tbls, 0,
						sizeof(struct xlat_ctx_tbls));

				/* Initialize the test structure */
				retval = xlat_ctx_cfg_init(&cfg, va_region,
							   &init_mmap[0U],
							   mmap_count, va_size);

				/*
				 * verify that the test setup is correct so far
				 */
				CHECK_TRUE(retval == 0);

				/* Test xlat_ctx_init() */
				retval = xlat_ctx_init(&ctx, &cfg, &tbls,
						       xlat_test_helpers_tbls(),
						       XLAT_TESTS_MAX_TABLES);

				/*
				 * verify that the test setup is correct so far
				 */
				CHECK_TRUE(retval == 0);

				validate_xlat_tables(&ctx, &tbl_idx[0U],
						     end_lvl);
			}
		}
	}
}

void xlat_get_llt_from_va_tc1(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_llt_info tbl_info, tbl_val;
	struct xlat_mmap_region init_mmap[3U];
	uint64_t start_va;
	size_t va_size, granularity;
	unsigned int mmap_count, index;
	xlat_addr_region_id_t va_region;
	int retval;
	unsigned int tbl_idx[3U];
	int base_lvl, end_lvl;
	unsigned int mmap_idx;
	uint64_t tte;
	uint64_t test_va;

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each possible base level, create a set of mmap regions
	 * ranging from level 1 or 0 (lowest level at which a valid walk
	 * can finish depending on whether FEAT_LPA2 is available) to
	 * XLAT_TABLE_LEVEL_MAX.
	 *
	 * For each possible (va_region, base_lvl, end_lvl) triplet,
	 * create 3 mappings that will correspond to a tte in the Last
	 * level Table. Then verify that the call to
	 * xlat_get_llt_from_va() is able to return the right
	 * xlat_tbl_info structure with the expected values.
	 ***************************************************************/

	mmap_count = 3U;
	va_region = (xlat_addr_region_id_t)test_helpers_get_rand_in_range(
						0UL, VA_REGIONS - 1);

	end_lvl = XLAT_MIN_BLOCK_LVL();
	for (; end_lvl <= XLAT_TABLE_LEVEL_MAX; end_lvl++) {

		for (base_lvl = XLAT_TEST_MIN_LVL();
		     base_lvl <= end_lvl;
		     base_lvl++) {

			/* Clean the data structures */
			memset((void *)&ctx, 0,
					sizeof(struct xlat_ctx));
			memset((void *)&cfg, 0,
					sizeof(struct xlat_ctx_cfg));
			memset((void *)&tbls, 0,
					sizeof(struct xlat_ctx_tbls));
			memset((void *)&tbl_info, 0,
					sizeof(struct xlat_llt_info));
			memset((void *)&tbl_val, 0,
					sizeof(struct xlat_llt_info));

			start_va = gen_va_space_params_by_lvl(base_lvl,
							      va_region,
							      &va_size);

			/*
			 * Use gen_mmap_array_by_level() to generate
			 * the mmap array.
			 */
			retval = gen_mmap_array_by_level(&init_mmap[0U],
							&tbl_idx[0U],
							mmap_count,
							base_lvl,
							end_lvl,
							&granularity,
							start_va,
							true);

			/* Ensure that so far the test setup is OK */
			CHECK_TRUE(retval == 0);

			retval = xlat_ctx_cfg_init(&cfg, va_region,
						   &init_mmap[0U],
						   mmap_count, va_size);

			/* Ensure that so far the test setup is OK */
			CHECK_TRUE(retval == 0);

			retval = xlat_ctx_init(&ctx, &cfg, &tbls,
					       xlat_test_helpers_tbls(),
					       XLAT_TESTS_MAX_TABLES);

			/* Ensure that so far the test setup is OK */
			CHECK_TRUE(retval == 0);

			for (mmap_idx = 0U; mmap_idx < mmap_count; mmap_idx++) {
				/*
				 * For each mmap region, pick up a
				 * random address for the test.
				 */
				test_va = init_mmap[mmap_idx].base_va
						+ ctx.cfg->base_va;
				test_va +=
					test_helpers_get_rand_in_range(0UL,
					init_mmap[mmap_idx].size - 1);

				/*
				 * Perform a table walk to retrieve
				 * table info. Store the expected values
				 * inside the validation xlat_llt_info
				 * structure.
				 */
				retval = xlat_test_helpers_table_walk(&ctx,
								test_va,
								&tte,
								&(tbl_val.table),
								&(tbl_val.level),
								&index);

				/*
				 * Calculate the expected base VA for the llt.
				 */
				tbl_val.llt_base_va = start_va;
				tbl_val.llt_base_va += (base_lvl < end_lvl) ?
					(XLAT_BLOCK_SIZE(base_lvl) *
							tbl_idx[mmap_idx]) : 0;

				/* Ensure that so far the test setup is OK */
				CHECK_TRUE(retval == 0);

				VERBOSE("\nTesting VA 0x%lx", test_va);

				/* Test xlat_get_llt_from_va */
				retval = xlat_get_llt_from_va(&tbl_info, &ctx,
								test_va);

				/* Check the return value */
				CHECK_TRUE(retval == 0);

				/*
				 * Validate the structure returned by
				 * xlat_get_llt_from_va
				 */
				MEMCMP_EQUAL((void *)&tbl_val,
					     (void *)&tbl_info,
					     sizeof(struct xlat_llt_info));
				VERBOSE(" : PASS\n\n");
			}
		}
	}
}

void xlat_get_llt_from_va_tc2(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_llt_info tbl_info;
	struct xlat_mmap_region init_mmap[3U];
	unsigned int tbl_idx[3U];
	size_t va_size, granularity;
	uint64_t start_va, test_va;
	xlat_addr_region_id_t va_region;
	int base_lvl, end_lvl;
	int retval;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Test xlat_get_llt_from_va() with a VAs ouside
	 * of the context VA space.
	 ***************************************************************/

	/*
	 * Pick up a base and end levels for the translation tables.
	 * The leves are arbitrary. Just to have a VA space enough
	 * for the tests.
	 */
	base_lvl = 2;
	end_lvl = 3;

	for (int i = 0U; i < VA_REGIONS; i++) {
		va_region = (xlat_addr_region_id_t)i;

		/*
		 * For the low region, the test will be executed
		 * only once, for a VA above the VA space limits.
		 *
		 * For the high region, the test will be executed twice:
		 *	- Once for VA below the VA space.
		 *	- Once of a VA above the VA space.
		 */
		for (unsigned int j = 0; j < (i + 1U); j++) {

			/* Clean the data structures */
			memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
			memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
			memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));
			memset((void *)&tbl_info, 0,
						sizeof(struct xlat_llt_info));

			/* Get VA space limits for Level 2 */
			start_va = gen_va_space_params_by_lvl(base_lvl, va_region,
							      &va_size);

			/*
			 * use gen_mmap_array_by_level() to generate
			 * the mmap for convenience.
			 */
			retval = gen_mmap_array_by_level(&init_mmap[0U],
							&tbl_idx[0U],
							3U, base_lvl, end_lvl,
							&granularity,
							start_va,
							true);

			/* Ensure that so far the test setup is OK */
			CHECK_TRUE(retval == 0);

			retval = xlat_ctx_cfg_init(&cfg, va_region,
						   &init_mmap[0U], 3U,
						   max_va_size);
			CHECK_TRUE(retval == 0);

			retval = xlat_ctx_init(&ctx, &cfg, &tbls,
					       xlat_test_helpers_tbls(),
					       XLAT_TESTS_MAX_TABLES);
			CHECK_TRUE(retval == 0);

			VERBOSE("\n");

			if (j == 0U) {
				/*
				 * VA above the VA space.
				 * The upper range of the address is arbitrary.
				 */
				test_va = (ctx.cfg->max_va_size) +
					test_helpers_get_rand_in_range(0UL,
					XLAT_BLOCK_SIZE(base_lvl) - 1);
			} else {
				/*
				 * VA below the VA space.
				 * The upper range of the address is arbitrary.
				 */
				test_va = test_helpers_get_rand_in_range(0UL,
					XLAT_BLOCK_SIZE(base_lvl) - 1);
			}

			/* Test xlat_get_llt_from_va */
			retval = xlat_get_llt_from_va(&tbl_info, &ctx, test_va);

			/* Check the return value */
			CHECK_VERBOSE((retval == -EFAULT),
				      "Testing VA 0x%lx", test_va);
			VERBOSE("\n");
		}
	}
}

void xlat_get_llt_from_va_tc3(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_llt_info tbl_info;
	struct xlat_mmap_region init_mmap[3U];
	unsigned int tbl_idx[3U];
	size_t va_size, granularity;
	uint64_t start_va, test_va;
	xlat_addr_region_id_t va_region;
	int base_lvl, end_lvl;
	int retval;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Test xlat_get_llt_from_va() with an unmapped VA belonging to
	 * the context VA space.
	 ***************************************************************/

	/*
	 * Pick up a base and end levels for the translation tables.
	 * The leves are arbitrary. Just to have a VA space enough
	 * for the tests.
	 */
	base_lvl = XLAT_TEST_MIN_LVL();
	end_lvl = 3;

	for (int i = 0U; i < VA_REGIONS; i++) {
		va_region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));
		memset((void *)&tbl_info, 0, sizeof(struct xlat_llt_info));

		/* VA space boundaries */
		start_va = gen_va_space_params_by_lvl(base_lvl, va_region,
						      &va_size);

		/*
		 * use gen_mmap_array_by_level() to generate
		 * the mmap for convenience, although we will
		 * only use one of the mmap regions (init_mmap[0]).
		 */
		retval = gen_mmap_array_by_level(&init_mmap[0U],
						&tbl_idx[0U],
						3U, base_lvl, end_lvl,
						&granularity,
						start_va,
						true);

		/* Ensure that so far the test setup is OK */
		CHECK_TRUE(retval == 0);

		retval = xlat_ctx_cfg_init(&cfg, va_region,
					   &init_mmap[0U], 3U,
					   max_va_size);
		CHECK_TRUE(retval == 0);

		retval = xlat_ctx_init(&ctx, &cfg, &tbls,
				       xlat_test_helpers_tbls(),
				       XLAT_TESTS_MAX_TABLES);
		CHECK_TRUE(retval == 0);

		VERBOSE("\n");

		test_va = ctx.cfg->base_va;
		test_va += (init_mmap[0U].base_va + init_mmap[0U].size);
		test_va += test_helpers_get_rand_in_range(1UL, PAGE_SIZE - 1UL);

		/* Test xlat_get_llt_from_va */
		retval = xlat_get_llt_from_va(&tbl_info, &ctx, test_va);

		/* Check the return value */
		CHECK_VERBOSE((retval == 0),
				      "Testing VA 0x%lx", test_va);
		VERBOSE("\n");
	}
}

void xlat_get_llt_from_va_prepare_assertion(struct xlat_ctx *ctx,
					    struct xlat_ctx_cfg *cfg,
					    struct xlat_ctx_tbls *tbls,
					    struct xlat_mmap_region *init_mmap)
{
	uint64_t start_va, end_va;
	xlat_addr_region_id_t va_region;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	assert(ctx != NULL);
	assert(cfg != NULL);
	assert(tbls != NULL);
	assert(init_mmap != NULL);

	va_region = (xlat_addr_region_id_t)test_helpers_get_rand_in_range(0UL,
							VA_REGIONS - 1U);

	/* Clean the data structures */
	memset((void *)ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)tbls, 0, sizeof(struct xlat_ctx_tbls));

	/* VA space boundaries */
	start_va = xlat_test_helpers_get_start_va(va_region, max_va_size);
	end_va = start_va + max_va_size - 1ULL;

	/* Generate a random mmap area */
	xlat_test_helpers_rand_mmap_array(init_mmap, 1U, start_va, end_va, true);

	(void)xlat_ctx_cfg_init(cfg, va_region, init_mmap, 1U, max_va_size);

	(void)xlat_ctx_init(ctx, cfg, tbls,
			    xlat_test_helpers_tbls(),
			    XLAT_TESTS_MAX_TABLES);
}

void xlat_get_llt_from_va_tc4(void)
{

	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region init_mmap;
	uint64_t test_va;

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Try calling xlat_get_llt_from_va() with a NULL
	 * xlat_llt_info structure
	 ***************************************************************/

	xlat_get_llt_from_va_prepare_assertion(&ctx, &cfg, &tbls, &init_mmap);

	test_va = ctx.cfg->base_va + init_mmap.base_va;

	/* Test xlat_get_llt_from_va */
	test_helpers_expect_assert_fail(true);
	(void)xlat_get_llt_from_va(NULL, &ctx, test_va);
	test_helpers_fail_if_no_assert_failed();
}

void xlat_get_llt_from_va_tc5(void)
{
	struct xlat_llt_info tbl_info;

	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Try calling xlat_get_llt_from_va() with a NULL
	 * xlat_ctx structure.
	 ***************************************************************/

	/* Clean the data structures */
	memset((void *)&tbl_info, 0, sizeof(struct xlat_llt_info));

	/* Test xlat_get_llt_from_va: NULL xlat_ctx */
	test_helpers_expect_assert_fail(true);
	(void)xlat_get_llt_from_va(&tbl_info, NULL, 0ULL);
	test_helpers_fail_if_no_assert_failed();
}

void xlat_get_llt_from_va_tc6(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_llt_info tbl_info;
	struct xlat_mmap_region init_mmap;
	uint64_t test_va;

	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Try calling xlat_get_llt_from_va() with a NULL
	 * xlat_ctx_cfg structure.
	 ***************************************************************/

	xlat_get_llt_from_va_prepare_assertion(&ctx, &cfg, &tbls, &init_mmap);
	memset((void *)&tbl_info, 0, sizeof(struct xlat_llt_info));

	test_va = ctx.cfg->base_va + init_mmap.base_va;

	/* Test xlat_get_llt_from_va: NULL xlat_ctx.cfg */
	ctx.cfg = NULL;
	test_helpers_expect_assert_fail(true);
	(void)xlat_get_llt_from_va(&tbl_info, &ctx, test_va);
	test_helpers_fail_if_no_assert_failed();
}

void xlat_get_llt_from_va_tc7(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_llt_info tbl_info;
	struct xlat_mmap_region init_mmap;
	uint64_t test_va;

	/***************************************************************
	 * TEST CASE 7:
	 *
	 * Try calling xlat_get_llt_from_va() with a NULL
	 * xlat_ctx_tbls structure.
	 ***************************************************************/

	xlat_get_llt_from_va_prepare_assertion(&ctx, &cfg, &tbls, &init_mmap);
	memset((void *)&tbl_info, 0, sizeof(struct xlat_llt_info));

	test_va = ctx.cfg->base_va + init_mmap.base_va;

	/* Test xlat_get_llt_from_va: NULL xlat_ctx.tbls */
	ctx.tbls = NULL;
	test_helpers_expect_assert_fail(true);
	(void)xlat_get_llt_from_va(&tbl_info, &ctx, test_va);
	test_helpers_fail_if_no_assert_failed();
}

void xlat_get_llt_from_va_tc8(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_llt_info tbl_info;
	struct xlat_mmap_region init_mmap;
	uint64_t test_va;

	/***************************************************************
	 * TEST CASE 8:
	 *
	 * Try calling xlat_get_llt_from_va() with an uninitialized
	 * xlat_ctx_cfg structure.
	 * Perform a full initialization of the context and then force
	 * 'ctx.cfg->initialized' to 'false' so we can ensure that
	 * this is what it is actually tested.
	 ***************************************************************/

	xlat_get_llt_from_va_prepare_assertion(&ctx, &cfg, &tbls, &init_mmap);
	memset((void *)&tbl_info, 0, sizeof(struct xlat_llt_info));

	test_va = ctx.cfg->base_va + init_mmap.base_va;

	/* Mark the cfg structure as not initialized */
	cfg.initialized = false;

	test_helpers_expect_assert_fail(true);
	(void)xlat_get_llt_from_va(&tbl_info, &ctx, test_va);
	test_helpers_fail_if_no_assert_failed();
}

void xlat_get_llt_from_va_tc9(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_llt_info tbl_info;
	struct xlat_mmap_region init_mmap;
	uint64_t test_va;

	/***************************************************************
	 * TEST CASE 9:
	 *
	 * Try calling xlat_get_llt_from_va() with an uninitialized
	 * xlat_ctx_tbls structure.
	 * Perform a full initialization of the context and then force
	 * 'ctx.tbls->initialized' to 'false' so we can ensure that
	 * this is what it is actually tested.
	 ***************************************************************/

	xlat_get_llt_from_va_prepare_assertion(&ctx, &cfg, &tbls, &init_mmap);
	memset((void *)&tbl_info, 0, sizeof(struct xlat_llt_info));

	test_va = ctx.cfg->base_va + init_mmap.base_va;

	/* Mark the tbls structure as not initialized */
	tbls.initialized = false;

	test_helpers_expect_assert_fail(true);
	(void)xlat_get_llt_from_va(&tbl_info, &ctx, test_va);
	test_helpers_fail_if_no_assert_failed();
}

void xlat_get_tte_ptr_tc1(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_llt_info tbl_info;
	struct xlat_mmap_region init_mmap[3U];
	unsigned int tbl_idx[3U];
	uint64_t start_va, test_va;
	xlat_addr_region_id_t va_region;
	unsigned int index;
	uint64_t *tte_ptr, *val_tte, *table;
	uint64_t tte;
	size_t granularity;
	int base_lvl, end_lvl;
	int level, retval;
	uint64_t max_va_size =	XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Initialize a translation context with a given VA space and
	 * 3 mmap regions at level 3. Then get a tte using
	 * xlat_get_tte_ptr() and verify that it is the correct entry.
	 *
	 * This test tries three different mmap areas per VA region:
	 *
	 *	- An address corresponding to the first entry at a
	 *	  last level table.
	 *	- An address corresponding to the last entry at a
	 *	  last level table.
	 *	- An address corresponding to an intermediate entry
	 *	  at a last level table.
	 *
	 * The test also tests 2 negative cases :
	 *	1. It tries to get the TTE via xlat_get_tte() for a lower
	 *	   VA  than the base VA.
	 *	2. It tries to get the TTE for a higher VA than is mapped
	 *	   by the last level table.
	 ***************************************************************/

	/*
	 * Pick up a base and end levels for the translation tables.
	 * The leves are arbitrary. Just to have a VA space enough
	 * for the tests.
	 */
	base_lvl = XLAT_TEST_MIN_LVL();
	end_lvl = 3;

	for (int i = 0U; i < VA_REGIONS; i++) {
		va_region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));
		memset((void *)&tbl_info, 0, sizeof(struct xlat_llt_info));

		/* VA space boundaries */
		start_va = xlat_test_helpers_get_start_va(va_region, max_va_size);

		/* Generate the mmap regions */
		retval = gen_mmap_array_by_level(&init_mmap[0U],
						&tbl_idx[0U],
						3U, base_lvl, end_lvl,
						&granularity,
						start_va, true);

		/* Ensure that so far the test setup is OK */
		CHECK_TRUE(retval == 0);

		retval = xlat_ctx_cfg_init(&cfg, va_region, &init_mmap[0U], 3U,
					   max_va_size);

		/* Ensure that so far the test setup is OK */
		CHECK_TRUE(retval == 0);

		retval = xlat_ctx_init(&ctx, &cfg, &tbls,
					xlat_test_helpers_tbls(),
					XLAT_TESTS_MAX_TABLES);

		/* Ensure that so far the test setup is OK */
		CHECK_TRUE(retval == 0);

		/* Get the xlat_llt_info structure used to look for TTEs */
		test_va = ctx.cfg->base_va + init_mmap[0].base_va;
		retval = xlat_get_llt_from_va(&tbl_info, &ctx, test_va);

		/* Ensure that so far the test setup is OK */
		CHECK_TRUE(retval == 0);

		/*
		 * Iterate over test VAs of all 3 mmap regions to
		 * test xlat_get_tte_ptr().
		 */
		VERBOSE("\n");
		for (unsigned int i = 0U; i < 3U; i++) {
			/*
			 * Get the xlat_llt_info structure used
			 * to look for TTEs.
			 */
			test_va = ctx.cfg->base_va + init_mmap[i].base_va;
			retval = xlat_get_llt_from_va(&tbl_info,
						      &ctx, test_va);

			/* Ensure that so far the test setup is OK */
			CHECK_TRUE(retval == 0);

			/*
			 * Add a random  offset to the current 'test_va'
			 * to be used for the tests.
			 */
			test_va += test_helpers_get_rand_in_range(0UL,
								PAGE_SIZE - 1);

			/*
			 * Perform a table walk to get the table containing
			 * the tte we are insterested in as well as the
			 * index of that tte in the table.
			 */
			retval = xlat_test_helpers_table_walk(&ctx, test_va,
							       &tte, &table,
							       &level, &index);
			/* Ensure that so far the test setup is OK */
			CHECK_TRUE(retval == 0);

			/* Get a pointer to the expected tte */
			val_tte = &table[index];

			/* Test xlat_get_tte_ptr() */
			tte_ptr = xlat_get_tte_ptr(&tbl_info, test_va);

			/* Validate the output */
			CHECK_VERBOSE((val_tte == tte_ptr),
				      "Testing VA 0x%lx", test_va);
		}

		/*
		 * test xlat_get_tte_ptr() agains a VA below the minimum
		 * VA mapped by 'tbl_info'. Use init_mmap[1] for this test.
		 */
		test_va = ctx.cfg->base_va + init_mmap[1U].base_va;
		retval = xlat_get_llt_from_va(&tbl_info, &ctx, test_va);

		/* Ensure that so far the test setup is OK */
		CHECK_TRUE(retval == 0);

		test_va = tbl_info.llt_base_va;
		test_va -= test_helpers_get_rand_in_range(1UL, PAGE_SIZE - 1UL);

		tte_ptr = xlat_get_tte_ptr(&tbl_info, test_va);

		/* Validate the output */
		CHECK_VERBOSE((tte_ptr == NULL),
			      "Check address 0x%lx against TT at VA 0x%lx",
			      test_va, tbl_info.llt_base_va);

		/*
		 * test xlat_get_tte_ptr() against a VA above the max
		 * VA mapped by 'tbl_info'. Use init_mmap[0] for this test.
		 */
		test_va = ctx.cfg->base_va + init_mmap[0U].base_va;
		retval = xlat_get_llt_from_va(&tbl_info, &ctx, test_va);

		/* Ensure that so far the test setup is OK */
		CHECK_TRUE(retval == 0);

		test_va = tbl_info.llt_base_va + XLAT_BLOCK_SIZE(tbl_info.level - 1);
		test_va += test_helpers_get_rand_in_range(1UL, PAGE_SIZE - 1UL);

		tte_ptr = xlat_get_tte_ptr(&tbl_info, test_va);

		/* Validate the output */
		CHECK_VERBOSE((tte_ptr == NULL),
			      "Check address 0x%lx against TT at VA 0x%lx",
			      test_va, tbl_info.llt_base_va);

		VERBOSE("\n");
	}
}

void xlat_get_tte_ptr_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Try to get a tte using xlat_get_tte() with a NULL
	 * xlat_llt_info structure.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)xlat_get_tte_ptr(NULL, 0ULL);
	test_helpers_fail_if_no_assert_failed();
}

void xlat_get_tte_ptr_tc3(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_llt_info tbl_info;
	struct xlat_mmap_region init_mmap;
	uint64_t test_va;

	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try to get a tte using xlat_get_tte() in which 'level' is
	 * below the minimum for the current architecture implementation.
	 ***************************************************************/

	xlat_get_llt_from_va_prepare_assertion(&ctx, &cfg, &tbls, &init_mmap);
	memset((void *)&tbl_info, 0, sizeof(struct xlat_llt_info));

	test_va = ctx.cfg->base_va + init_mmap.base_va;

	/* Override the xlat_llt_info structure's level field */
	tbl_info.level = XLAT_TABLE_LEVEL_MIN - 1;

	test_helpers_expect_assert_fail(true);
	(void)xlat_get_tte_ptr(&tbl_info, test_va);
	test_helpers_fail_if_no_assert_failed();
}

void xlat_get_tte_ptr_tc4(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_llt_info tbl_info;
	struct xlat_mmap_region init_mmap;
	uint64_t test_va;

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Try to get a tte using xlat_get_tte() in which 'level' is
	 * above the maximum for the current architecture implementation.
	 ***************************************************************/

	xlat_get_llt_from_va_prepare_assertion(&ctx, &cfg, &tbls, &init_mmap);
	memset((void *)&tbl_info, 0, sizeof(struct xlat_llt_info));

	test_va = ctx.cfg->base_va + init_mmap.base_va;

	/* Override the xlat_llt_info structure's level field */
	tbl_info.level = XLAT_TABLE_LEVEL_MAX + 1;

	test_helpers_expect_assert_fail(true);
	(void)xlat_get_tte_ptr(&tbl_info, test_va);
	test_helpers_fail_if_no_assert_failed();
}

void xlat_unmap_memory_page_tc1(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uint64_t start_va;
	size_t va_size, granularity;
	unsigned int mmap_count;
	xlat_addr_region_id_t va_region;
	int retval;
	struct xlat_mmap_region init_mmap[3U];
	unsigned int tbl_idx[3U];
	int base_lvl, end_lvl;

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each possible end lookup level, create a set transient
	 * valid random mappings.
	 *
	 * For each possible (va_region, end_lvl) tuple, there will be
	 * three mmap regions created:
	 *
	 *	- First region mapped at the beginning of a table whose
	 *	  final lookup level is 'end_lvl'
	 *	- Second region mapped at a random tte of a table whose
	 *	  final lookup level is 'end_lvl'
	 *	- Third region mapped at the end of a table whose
	 *	  final lookup level is 'end_lvl'
	 *
	 * Then verify that the tables can be unmapped and that the
	 * resulting tte will contain a transient invalid entry.
	 ***************************************************************/

	mmap_count = 3;
	base_lvl = XLAT_TEST_MIN_LVL();

	end_lvl = XLAT_MIN_BLOCK_LVL();
	for (; end_lvl <= XLAT_TABLE_LEVEL_MAX; end_lvl++) {
		for (int i = 0U; i < VA_REGIONS; i++) {
			va_region = (xlat_addr_region_id_t)i;

			start_va = gen_va_space_params_by_lvl(base_lvl,
							      va_region,
							      &va_size);

			retval = gen_mmap_array_by_level(&init_mmap[0U],
							 &tbl_idx[0U],
							 mmap_count,
							 base_lvl,
							 end_lvl,
							 &granularity,
							 start_va,
							 false);

			/* Verify that the test setup is correct so far */
			CHECK_TRUE(retval == 0);

			/* Clean the data structures */
			memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
			memset((void *)&cfg, 0,	sizeof(struct xlat_ctx_cfg));
			memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

			/* Initialize the test structure */
			retval = xlat_ctx_cfg_init(&cfg, va_region,
						   &init_mmap[0U],
						   mmap_count, va_size);

			/* Verify that the test setup is correct so far */
			CHECK_TRUE(retval == 0);

			retval = xlat_ctx_init(&ctx, &cfg, &tbls,
					       xlat_test_helpers_tbls(),
					       XLAT_TESTS_MAX_TABLES);

			/* Verify that the test setup is correct so far */
			CHECK_TRUE(retval == 0);

			/*
			 * For each one of the mmap regions:
			 * - get the TTE of a random VA and make it transient
			 * - call xlat_unmap_memory_page() over the same VA
			 * - verify that the TTE is now transient invalid.
			 */
			for (unsigned int j = 0U; j < mmap_count; j++) {
				uint64_t tte;
				uint64_t *tbl_ptr;
				unsigned int tte_idx;
				int tte_lvl;
				struct xlat_llt_info tbl_info;
				uint64_t offset =
					test_helpers_get_rand_in_range(0UL,
								PAGE_SIZE - 1);
				uint64_t test_va = init_mmap[j].base_va +
						ctx.cfg->base_va + offset;

				/*
				 * Perform a table walk to retrieve the table
				 * where the VA is mapped along with the index
				 * of the TTE within the table.
				 */
				retval = xlat_test_helpers_table_walk(&ctx,
							test_va, &tte,
							&tbl_ptr, &tte_lvl,
							&tte_idx);

				/*
				 * Verify that the test setup is correct so far
				 */
				CHECK_TRUE(retval == 0);

				/*
				 * The TTE is expected to be valid. Make it
				 * transient valid within the table.
				 */
				tbl_ptr[tte_idx] |=
					(1ULL << TRANSIENT_FLAG_SHIFT);

				/*
				 * Retrieve the xlat_llt_info structure needed
				 * to feed xlat_unmap_memory_page()
				 */
				retval = xlat_get_llt_from_va(&tbl_info, &ctx,
								test_va);

				/*
				 * Verify that the test setup is correct so far
				 */
				CHECK_TRUE(retval == 0);

				/*
				 * Try to unmap the page/block
				 * containing `test_va`
				 */
				retval = xlat_unmap_memory_page(&tbl_info,
								test_va);

				/* Verify that the return is as expected */
				CHECK_TRUE(retval == 0);

				/*
				 * Verify that the TTE is marked as transient
				 * invalid.
				 */
				CHECK_VERBOSE((tbl_ptr[tte_idx] ==
					TRANSIENT_DESC),
					"Verifying TTE for VA 0x%lx is marked as Transient Invalid",
						test_va);
			}
			VERBOSE("\n");
		}
	}
}

void xlat_unmap_memory_page_tc2(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uint64_t start_va, test_va;
	size_t va_size, granularity;
	unsigned int mmap_count;
	unsigned int tte_idx;
	xlat_addr_region_id_t va_region;
	int retval, tte_lvl;
	struct xlat_mmap_region init_mmap[3U];
	unsigned int tbl_idx[3U];
	struct xlat_llt_info tbl_info;
	uint64_t tte, val_tte;
	uint64_t *tbl_ptr;
	int base_lvl, end_lvl;

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Generate a mmap region with a set of transient valid
	 * mappings. Then run a set of negative tests:
	 *
	 *	- Try addresses below and above the range mapped by the
	 *	  xlat_llt_info structure on a transient-valid entry.
	 *	- Try unmapping from a valid non-transient entry.
	 *	- Try unmapping from an invalid entry.
	 ***************************************************************/

	/*
	 * Pick up a base and end levels for the translation tables.
	 * The leves are arbitrary. Just to have a VA space enough
	 * for the tests.
	 */
	base_lvl = XLAT_TEST_MIN_LVL();
	end_lvl = 3;

	mmap_count = 3U;

	for (int i = 0U; i < VA_REGIONS; i++) {
		va_region = (xlat_addr_region_id_t)i;

		start_va = gen_va_space_params_by_lvl(base_lvl,
						      va_region, &va_size);

		/*
		 * We generate the mmap regions to use. We will be interested
		 * in init_mmap[1].
		 */
		retval = gen_mmap_array_by_level(&init_mmap[0U], &tbl_idx[0U],
						 mmap_count, base_lvl, end_lvl,
						 &granularity,
						 start_va, false);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0,	sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, va_region, &init_mmap[0U],
					   mmap_count, va_size);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		retval = xlat_ctx_init(&ctx, &cfg, &tbls,
				       xlat_test_helpers_tbls(),
				       XLAT_TESTS_MAX_TABLES);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/*
		 * Make the TTEs of the mapped region, which is expected
		 * to be valid, transient valid.
		 */
		test_va = init_mmap[1U].base_va + ctx.cfg->base_va;

		/*
		 * Perform a table walk to retrieve the table where the VA
		 * is mapped along with the index of the TTE within the table.
		 */
		retval = xlat_test_helpers_table_walk(&ctx, test_va, &tte,
						      &tbl_ptr, &tte_lvl,
						      &tte_idx);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/*
		 * The TTE is expected to be valid. Make it
		 * transient valid within the table.
		 */
		tbl_ptr[tte_idx] |= (1ULL << TRANSIENT_FLAG_SHIFT);
		val_tte = tbl_ptr[tte_idx];

		/*
		 * Retrieve the xlat_llt_info structure needed to feed
		 * xlat_unmap_memory_page().
		 */
		retval = xlat_get_llt_from_va(&tbl_info, &ctx,
				init_mmap[1U].base_pa + ctx.cfg->base_va);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/*
		 * Test xlat_unmmap_memory_page() with a valid address
		 * below the start of init_mmap[0U]. This gives us an address
		 * below the range mapped by table we retrieved.
		 */
		test_va = init_mmap[0U].base_va + ctx.cfg->base_va;
		test_va -= test_helpers_get_rand_in_range(1UL, PAGE_SIZE - 1UL);

		/* Try to unmap the page/block containing `test_va` */
		retval = xlat_unmap_memory_page(&tbl_info, test_va);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%lx on TTE for VA 0x%lx",
			      test_va,
			      init_mmap[1U].base_va + ctx.cfg->base_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);

		/*
		 * Repeat the process, this time with an address on a page
		 * after the one mapped by init_mmap[2U]. This gives us an
		 * address over the range mapped by table we retrieved.
		 */
		test_va = init_mmap[2U].base_va + ctx.cfg->base_va;
		test_va += PAGE_SIZE;
		test_va += test_helpers_get_rand_in_range(0UL, PAGE_SIZE - 1UL);

		/* Try to unmap the page/block containing `test_va` */
		retval = xlat_unmap_memory_page(&tbl_info, test_va);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%lx on TTE for VA 0x%lx",
			      test_va,
			      init_mmap[2U].base_va + ctx.cfg->base_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);

		/*
		 * Try to unmap an address marked as non-transient
		 */
		tbl_ptr[tte_idx] &= ~(MASK(TRANSIENT_FLAG));
		val_tte = tbl_ptr[tte_idx];

		test_va = init_mmap[1U].base_va + ctx.cfg->base_va;
		test_va += test_helpers_get_rand_in_range(0UL, PAGE_SIZE - 1UL);

		/* Try to unmap the page/block containing `test_va` */
		retval = xlat_unmap_memory_page(&tbl_info, test_va);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%lx on a non-transient valid TTE",
			      test_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);

		/*
		 * Try to unmap an address marked as invalid.
		 */
		tbl_ptr[tte_idx] = INVALID_DESC;
		val_tte = tbl_ptr[tte_idx];

		test_va = init_mmap[1U].base_va + ctx.cfg->base_va;
		test_va += test_helpers_get_rand_in_range(0UL, PAGE_SIZE - 1UL);

		/* Try to unmap the page/block containing `test_va` */
		retval = xlat_unmap_memory_page(&tbl_info, test_va);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%lx on a ninvalid TTE",
			      test_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);
		VERBOSE("\n");
	}
}

void xlat_unmap_memory_page_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try calling xlat_unmap_memory_page with a NULL
	 * xlat_llt_info structure.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)xlat_unmap_memory_page(NULL, 0ULL);
	test_helpers_fail_if_no_assert_failed();
}

void xlat_map_memory_page_with_attrs_tc1(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uint64_t start_va;
	size_t va_size, granularity;
	unsigned int mmap_count;
	xlat_addr_region_id_t va_region;
	int retval;
	struct xlat_mmap_region init_mmap[3U];
	unsigned int tbl_idx[3U];
	int base_lvl, end_lvl;

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each possible end lookup level, create a set transient
	 * random mappings.
	 *
	 * For each possible (va_region, end_lvl) tuple, there will be three
	 * mmap regions created:
	 *
	 *	- First region mapped at the beginning of a table whose
	 *	  final lookup level is 'end_lvl'
	 *	- Second region mapped at a random index of a table whose
	 *	  final lookup level is 'end_lvl'
	 *	- Third region mapped at the end of a table whose
	 *	  final lookup level is 'end_lvl'
	 *
	 * Then verify that we can map PA areas into the transient
	 * entries using random attributes and that the generated
	 * entry is valid.
	 ***************************************************************/

	mmap_count = 3;
	base_lvl = XLAT_TEST_MIN_LVL();

	end_lvl = XLAT_MIN_BLOCK_LVL();
	for (; end_lvl <= XLAT_TABLE_LEVEL_MAX; end_lvl++) {
		for (int i = 0U; i < VA_REGIONS; i++) {
			va_region = (xlat_addr_region_id_t)i;

			start_va = gen_va_space_params_by_lvl(base_lvl,
							      va_region,
							      &va_size);

			retval = gen_mmap_array_by_level(&init_mmap[0U],
							 &tbl_idx[0U],
							 mmap_count,
							 base_lvl,
							 end_lvl,
							 &granularity,
							 start_va,
							 false);

			/* Verify that the test setup is correct so far */
			CHECK_TRUE(retval == 0);

			/* Force all the mmap regions to be TRANSIENT */
			for (unsigned int j = 0U; j < mmap_count; j++) {
				init_mmap[j].attr = MT_TRANSIENT;
			}

			/* Clean the data structures */
			memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
			memset((void *)&cfg, 0,	sizeof(struct xlat_ctx_cfg));
			memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

			/* Initialize the test structure */
			retval = xlat_ctx_cfg_init(&cfg, va_region,
						   &init_mmap[0U],
						   mmap_count, va_size);

			/* Verify that the test setup is correct so far */
			CHECK_TRUE(retval == 0);

			retval = xlat_ctx_init(&ctx, &cfg, &tbls,
					       xlat_test_helpers_tbls(),
					       XLAT_TESTS_MAX_TABLES);

			/* Verify that the test setup is correct so far */
			CHECK_TRUE(retval == 0);

			/*
			 * For each one of the mmap regions:
			 * - Generate a random VA within the mmap VA space.
			 * - generate a set of random attributes.
			 * - Map a random PA to the generated VA and with
			 *   the generated attributes.
			 * - call xlat_unmap_memory_page_map_with_attrs() to
			 *   create the mapping.
			 * - verify that the new entry is valid.
			 */
			for (unsigned int j = 0U; j < mmap_count; j++) {
				uint64_t tte, val_tte, attrs, pa, type;
				uint64_t *tbl_ptr;
				unsigned int tte_idx;
				int tte_lvl;
				struct xlat_llt_info tbl_info;
				uint64_t offset =
					test_helpers_get_rand_in_range(0UL,
							init_mmap[i].size - 1);
				uint64_t test_va = init_mmap[j].base_va +
						ctx.cfg->base_va + offset;

				/*
				 * Perform a table walk to retrieve the table
				 * where the VA is mapped along with the index
				 * of the TTE within the table.
				 */
				retval = xlat_test_helpers_table_walk(&ctx,
							test_va, &tte,
							&tbl_ptr, &tte_lvl,
							&tte_idx);

				/*
				 * Verify that the test setup is correct so far
				 */
				CHECK_TRUE(retval == 0);

				/* Generate a random set of attributes.	*/
				do {
					attrs = xlat_test_helpers_rand_mmap_attrs(true);
				} while (attrs == MT_TRANSIENT);

				/*
				 * Generate the validation TTE. For convenience,
				 * create an identity mapping.
				 */
				retval = xlat_test_helpers_gen_attrs(&val_tte,
								     attrs);
				pa = init_mmap[j].base_va & XLAT_TEST_GET_PA_MASK();

				/*
				 * Add an arbitrary offset to PA to be passed to
				 * xlat_map_memory_page_with_attrs()
				 */
				pa += test_helpers_get_rand_in_range(1UL,
						XLAT_BLOCK_SIZE(end_lvl) - 1);
				val_tte |= set_oa_to_tte(pa &
						XLAT_ADDR_MASK(end_lvl));

				/* The TTE will be a transient one */
				val_tte |= (1ULL <<
					TRANSIENT_FLAG_SHIFT);

				/* TTE type */
				type = (end_lvl == XLAT_TABLE_LEVEL_MAX) ?
							PAGE_DESC :
							BLOCK_DESC;
				val_tte |= type;

				/* Verify the test setup */
				CHECK_TRUE(retval == 0);

				/*
				 * Retrieve the xlat_llt_info structure needed
				 * to feed xlat_map_memory_page_with_attrs()
				 */
				retval = xlat_get_llt_from_va(&tbl_info, &ctx,
								test_va);

				/*
				 * Verify that the test setup is correct so far
				 */
				CHECK_TRUE(retval == 0);

				/*
				 * Try to map the PA with the attributes to the
				 * `test_va`
				 */
				retval = xlat_map_memory_page_with_attrs(
							&tbl_info,
							test_va, pa, attrs);

				/* Verify that the return is as expected */
				CHECK_VERBOSE((retval == 0),
					"Mapping PA 0x%.16lx to VA 0x%.16lx with attrs 0x%lx",
					 pa, test_va, attrs);
				CHECK_TRUE(retval == 0);

				/*
				 * Verify that the generated TTE matches
				 * the validation one.
				 */
				CHECK_VERBOSE((val_tte == tbl_ptr[tte_idx]),
					"Verifying TTE 0x%.16lx against 0x%.16lx",
						tbl_ptr[tte_idx], val_tte);
			}
			VERBOSE("\n");
		}
	}
}

void xlat_map_memory_page_with_attrs_tc2(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uint64_t start_va, test_va, test_pa;
	size_t va_size, granularity;
	unsigned int mmap_count;
	unsigned int tte_idx;
	xlat_addr_region_id_t va_region;
	int tte_lvl, retval;
	struct xlat_mmap_region init_mmap[3U];
	unsigned int tbl_idx[3U];
	struct xlat_llt_info tbl_info;
	uint64_t tte, val_tte;
	uint64_t *tbl_ptr;
	int base_lvl, end_lvl;
	unsigned int pa_range_bits_arr[] = {
		PARANGE_0000_WIDTH, PARANGE_0001_WIDTH, PARANGE_0010_WIDTH,
		PARANGE_0011_WIDTH, PARANGE_0100_WIDTH, PARANGE_0101_WIDTH,
		PARANGE_0110_WIDTH
	};
	unsigned int parange_index =
			(unsigned int)test_helpers_get_rand_in_range(0UL,
					ARRAY_SIZE(pa_range_bits_arr) - 1U);
	uint64_t id_aa64mmfr0_el1 = read_id_aa64mmfr0_el1();

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Generate a mmap region with a set of transient invalid
	 * mappings. Then run a set of negative tests:
	 *
	 *	- Try addresses below and above the range mapped by the
	 *	  xlat_llt_info structure on a transient-invalid entry.
	 *	- Try mapping a PA lager than the maximum supported PA
	 *	  to a transient-invalid entry.
	 *	- Try mapping to a transient-valid entry.
	 *	- Try mapping to a valid entry.
	 *	- Try mapping to an invalid entry.
	 ***************************************************************/

	/*
	 * Pick up a base and end levels for the translation tables.
	 * The leves are arbitrary. Just to have a VA space enough
	 * for the tests.
	 */
	base_lvl = XLAT_TEST_MIN_LVL();
	end_lvl = 3;

	mmap_count = 3U;

	for (int i = 0U; i < VA_REGIONS; i++) {
		va_region = (xlat_addr_region_id_t)i;

		start_va = gen_va_space_params_by_lvl(base_lvl,
						      va_region, &va_size);

		/*
		 * We generate the mmap regions to use. We will be interested
		 * in init_mmap[1] for the transient-invalid tests and in
		 * init_mmap[2] for the rest of tests.
		 */
		retval = gen_mmap_array_by_level(&init_mmap[0U], &tbl_idx[0U],
						 mmap_count, base_lvl, end_lvl,
						 &granularity,
						 start_va, false);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/* Force init_mmap[1] to be TRANSIENT */
		init_mmap[1U].attr = MT_TRANSIENT;

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0,	sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, va_region, &init_mmap[0U],
					   mmap_count, va_size);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		retval = xlat_ctx_init(&ctx, &cfg, &tbls,
				       xlat_test_helpers_tbls(),
				       XLAT_TESTS_MAX_TABLES);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		test_va = init_mmap[1U].base_va + ctx.cfg->base_va;

		/*
		 * Retrieve the xlat_llt_info structure needed to feed
		 * xlat_map_memory_page_with_attrs().
		 */
		retval = xlat_get_llt_from_va(&tbl_info, &ctx, test_va);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/*
		 * Test xlat_map_memory_page_with_attrs() with a valid address
		 * within init_mmap[0]. This gives us an address
		 * below the range mapped by table we retrieved (which belongs
		 * to init_mmap[1]). For simplicity, set the attributes and
		 * the PA both to 0x0.
		 */
		test_va = init_mmap[0U].base_va + ctx.cfg->base_va;
		test_va += test_helpers_get_rand_in_range(0UL,
						init_mmap[0U].size - 1);

		/* Try to map to the page/block containing `test_va` */
		retval = xlat_map_memory_page_with_attrs(&tbl_info, test_va,
							 0ULL, 0ULL);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%.16lx on TTE for VA 0x%.16lx",
			      test_va,
			      init_mmap[1U].base_va + ctx.cfg->base_va);

		/*
		 * Repeat the process, this time with an address on a page
		 * mapped by init_mmap[2]. This gives us an
		 * address over the range mapped by table we retrieved.
		 */
		test_va = init_mmap[2U].base_va + ctx.cfg->base_va;
		test_va += test_helpers_get_rand_in_range(0UL, PAGE_SIZE - 1UL);

		/* Try to map to the page/block containing `test_va` */
		retval = xlat_map_memory_page_with_attrs(&tbl_info, test_va,
							 0ULL, 0ULL);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%.16lx on TTE for VA 0x%.16lx",
			      test_va,
			      init_mmap[2U].base_va + ctx.cfg->base_va);

		/*
		 * Test with a PA larger than the maximum PA supported.
		 */

		/* Configure a random maximum PA supported */
		xlat_test_helpers_set_parange(parange_index);
		test_pa =
			(1ULL << pa_range_bits_arr[parange_index]) + PAGE_SIZE;

		test_va = init_mmap[1U].base_va + ctx.cfg->base_va;

		/*
		 * Perform a table walk to retrieve the table where the VA
		 * is mapped along with the index of the TTE within the table.
		 */
		retval = xlat_test_helpers_table_walk(&ctx, test_va, &tte,
						      &tbl_ptr, &tte_lvl,
						      &tte_idx);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/*
		 * Take a snapshot of the TTE. This will be used to verify
		 * that the TTE hasn't been altered.
		 */
		val_tte = tbl_ptr[tte_idx];

		/* Get a random address to test */
		test_va += test_helpers_get_rand_in_range(0UL, PAGE_SIZE - 1UL);

		/* Try to map the PA to the page/block containing `test_va` */
		retval = xlat_map_memory_page_with_attrs(&tbl_info, test_va,
							 test_pa, 0ULL);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing PA 0x%.16lx on with a max supported PA of 0x%.16llx",
			      test_pa,
			      (1ULL << pa_range_bits_arr[parange_index]) - 1ULL);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);

		/* Restore the maximum supported PA size for next tests */
		host_write_sysreg("id_aa64mmfr0_el1", id_aa64mmfr0_el1);

		/* The rest of the tests will be based on init_mmap[2] */
		test_va = init_mmap[2U].base_va + ctx.cfg->base_va;

		/*
		 * Perform a table walk to retrieve the table where the VA
		 * is mapped along with the index of the TTE within the table.
		 */
		retval = xlat_test_helpers_table_walk(&ctx, test_va, &tte,
						      &tbl_ptr, &tte_lvl,
						      &tte_idx);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/*
		 * Retrieve the xlat_llt_info structure needed to feed
		 * xlat_map_memory_page_with_attrs().
		 */
		retval = xlat_get_llt_from_va(&tbl_info, &ctx, test_va);

		/* Verify that the test setup is correct so far */
		CHECK_TRUE(retval == 0);

		/*
		 * Make the TTEs of the mapped region, which is expected
		 * to be valid, transient valid.
		 */
		tbl_ptr[tte_idx] |= (1ULL << TRANSIENT_FLAG_SHIFT);

		/*
		 * Take a snapshot of the TTE. This will be used to verify
		 * that the TTE hasn't been altered.
		 */
		val_tte = tbl_ptr[tte_idx];

		/*
		 * Now try to map a valid VA. In this case the associated
		 * TTE will contain a transient valid mapping.
		 */
		test_va = init_mmap[2U].base_va + ctx.cfg->base_va;
		test_va += test_helpers_get_rand_in_range(0UL, PAGE_SIZE - 1UL);

		/* Try to map to the page/block containing `test_va` */
		retval = xlat_map_memory_page_with_attrs(&tbl_info, test_va,
							 0ULL, 0ULL);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%.16lx on a transient valid TTE",
			      test_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);

		/*
		 * Repeat the last test but after clearing the TRANSIENT
		 * flag from the TTE. This will test the behaviour with
		 * a non transient TTE.
		 */
		tbl_ptr[tte_idx] &= ~(1ULL << TRANSIENT_FLAG_SHIFT);
		val_tte = tbl_ptr[tte_idx];

		test_va = init_mmap[2U].base_va + ctx.cfg->base_va;
		test_va += test_helpers_get_rand_in_range(0UL, PAGE_SIZE - 1UL);

		/* Try to map to the page/block containing `test_va` */
		retval = xlat_map_memory_page_with_attrs(&tbl_info, test_va,
							 0ULL, 0ULL);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%.16lx on a valid TTE",
			      test_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);

		/*
		 * Repeat the last test on an INVALID TTE.
		 */
		tbl_ptr[tte_idx] = 0ULL;
		val_tte = 0ULL;

		test_va = init_mmap[2U].base_va + ctx.cfg->base_va;
		test_va += test_helpers_get_rand_in_range(0UL, PAGE_SIZE - 1UL);

		/* Try to map to the page/block containing `test_va` */
		retval = xlat_map_memory_page_with_attrs(&tbl_info, test_va,
							 0ULL, 0ULL);

		/* Verify that the return is as expected */
		CHECK_VERBOSE((retval == -EFAULT),
			      "Testing VA 0x%.16lx on an invalid TTE",
			      test_va);

		/* Verify that the TTE remains unchanged */
		CHECK_EQUAL(val_tte, tbl_ptr[tte_idx]);

		VERBOSE("\n");
	}
}

void xlat_map_memory_page_with_attrs_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try calling xlat_map_memory_page_with_attrs with a NULL
	 * xlat_llt_info structure.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)xlat_map_memory_page_with_attrs(NULL, 0ULL, 0ULL, 0ULL);
	test_helpers_fail_if_no_assert_failed();
}

/* Helper function to validate ttbrx_el2 registers */
static void validate_ttbrx_el2(struct xlat_ctx *ctx)
{
	uint64_t expected_ttbrx, ttbrx;
	xlat_addr_region_id_t va_region;

	assert(ctx != NULL);

	va_region = ctx->cfg->region;

	/* BADDR */
	expected_ttbrx = ((uint64_t)&ctx->tbls->tables[0U]) &
						MASK(TTBRx_EL2_BADDR);

	ttbrx = read_ttbr1_el2();
	if (va_region == VA_LOW_REGION) {
		ttbrx = read_ttbr0_el2();

		/*
		 * CnP bit. It is expected that the xlat library will
		 * automatically set this bit for the low region.
		 */
		expected_ttbrx |= (1ULL << TTBRx_EL2_CnP_SHIFT);
	}

	CHECK_VERBOSE((expected_ttbrx == ttbrx),
		       "Expected TTBR%c_EL2: 0x%lx - Received: 0x%lx",
						(unsigned int)va_region + '0',
						expected_ttbrx, ttbrx);
}

/* Helper function to validate TCR_EL2 register */
static void validate_tcr_el2(struct xlat_ctx *low_ctx,
			     struct xlat_ctx *high_ctx)
{
	uint64_t exp_tcr, tcr;
	size_t t0sz, t1sz;
	unsigned int parange;

	tcr = read_tcr_el2();

	/*
	 * Calculate the VA space size for both contexts based on
	 * the TCR_EL2 register.
	 */
	t0sz = ((size_t)1) << (64U - EXTRACT(TCR_EL2_T0SZ, tcr));
	t1sz = ((size_t)1) << (64U - EXTRACT(TCR_EL2_T1SZ, tcr));

	/* Validate the VA space size of the contexts */
	CHECK_VERBOSE((t0sz == low_ctx->cfg->max_va_size),
		      "Check VA space size for Low Region: 0x%lx == 0x%lx",
		      t0sz, low_ctx->cfg->max_va_size);
	CHECK_VERBOSE((t1sz == high_ctx->cfg->max_va_size),
		      "Check VA space size for High Region: 0x%lx == 0x%lx",
		      t1sz, high_ctx->cfg->max_va_size);

	/* Mask out TxSZ fields. We have already validated them */
	tcr &= ~(MASK(TCR_EL2_T0SZ) | MASK(TCR_EL2_T1SZ));

	/*
	 * Inner and outher cacheability attributes as expected by RMM
	 * for all the contexts.
	 */
	exp_tcr = TCR_EL2_IRGN0_WBWA | TCR_EL2_ORGN0_WBWA;
	exp_tcr |= TCR_EL2_IRGN1_WBWA | TCR_EL2_ORGN1_WBWA;

	/* Shareability as expected by RMM for all the contexts */
	exp_tcr |= TCR_EL2_SH0_IS | TCR_EL2_SH1_IS;

	/* Granule size for all the contexts. Only 4KB supported */
	exp_tcr |= TCR_EL2_TG0_4K | TCR_EL2_TG1_4K;

	/* Hierarchical permissions */
	exp_tcr |= TCR_EL2_AS | TCR_EL2_HPD0 | TCR_EL2_HPD1;

	/*
	 * Xlat library configures TCR_EL2.IPS to the max
	 * supported by the PE.
	 */
	parange = EXTRACT(ID_AA64MMFR0_EL1_PARANGE, read_id_aa64mmfr0_el1());
	exp_tcr |= INPLACE(TCR_EL2_IPS, parange);

	if (is_feat_lpa2_4k_present() == true) {
		exp_tcr |= (TCR_EL2_DS_LPA2_EN
			    | TCR_EL2_SH0_IS
			    | TCR_EL2_SH1_IS);
	}

	/* Validate tcr_el2*/
	CHECK_VERBOSE((exp_tcr == tcr),
		      "Validate TCR_EL2 against expected value: Read 0x%.16lx - Expected 0x%.16lx",
		      tcr, exp_tcr);
}

void xlat_arch_setup_mmu_cfg_tc1(void)
{
	struct xlat_ctx ctx[2U];
	struct xlat_ctx_cfg cfg[2U];
	struct xlat_ctx_tbls tbls[2U];
	uint64_t *base_tbl[2U], *xlat_tables;
	uint64_t start_va, end_va;
	xlat_addr_region_id_t va_region;
	int retval;
	struct xlat_mmap_region init_mmap[2U];
	unsigned int pa_index, max_pa_index;
	bool lpa2 = is_feat_lpa2_4k_present();
	unsigned int pa_range_bits_arr[] = {
		PARANGE_0000_WIDTH, PARANGE_0001_WIDTH, PARANGE_0010_WIDTH,
		PARANGE_0011_WIDTH, PARANGE_0100_WIDTH, PARANGE_0101_WIDTH,
		PARANGE_0110_WIDTH
	};
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();
	struct xlat_mmu_cfg mmu_config;

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Generate a translation context for each region and configure
	 * the MMU registers based on both contexts. Verify that the
	 * right parameters have been configured.
	 ***************************************************************/

	max_pa_index = ARRAY_SIZE(pa_range_bits_arr);
	max_pa_index = (lpa2 == true) ? max_pa_index : max_pa_index - 1U;
	pa_index = (unsigned int)test_helpers_get_rand_in_range(0UL,
							max_pa_index - 1U);

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx) * 2U);
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg) * 2U);
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls) * 2U);

	/* Configure a random maximum PA supported */
	xlat_test_helpers_set_parange(pa_index);

	for (int i = 0U; i < VA_REGIONS; i++) {
		va_region = (xlat_addr_region_id_t)i;

		xlat_tables = xlat_test_helpers_tbls();
		/* Use half of the available tables for each region */
		base_tbl[i] = &xlat_tables[(i * XLAT_TESTS_MAX_TABLES *
						XLAT_TABLE_ENTRIES) >> 1U];
		/* VA space boundaries */
		start_va = xlat_test_helpers_get_start_va(va_region,
							  max_va_size);
		end_va = start_va + max_va_size - 1ULL;

		/* Generate only a single mmap region for each region */
		xlat_test_helpers_rand_mmap_array(&init_mmap[i], 1U, start_va, end_va, true);

		retval = xlat_ctx_cfg_init(&cfg[i], va_region, &init_mmap[i],
					   1U, max_va_size);
		CHECK_TRUE(retval == 0);

		retval = xlat_ctx_init(&ctx[i], &cfg[i], &tbls[i],
				       base_tbl[i], XLAT_TESTS_MAX_TABLES >> 1U);
		CHECK_TRUE(retval == 0);

		/* Initialize MMU for the given context */
		retval = xlat_arch_setup_mmu_cfg(&ctx[i], &mmu_config);

		/* Verify that the MMU has been configured */
		CHECK_TRUE(retval == 0);

		/* Write the MMU config for the given context */
		xlat_arch_write_mmu_cfg(&mmu_config);

		/* Validate TTBR_EL2 for each context */
		validate_ttbrx_el2(&ctx[i]);
	}

	/* Validate TCR_EL2 for both contexts at the same time */
	validate_tcr_el2(&ctx[0U], &ctx[1U]);
}

void xlat_arch_setup_mmu_cfg_tc2(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uint64_t start_va, end_va;
	int retval;
	struct xlat_mmap_region init_mmap;
	uint64_t max_va_size =	XLAT_TEST_MAX_VA_SIZE();
	struct xlat_mmu_cfg mmu_config;

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Generate a valid translation context for one of the regions
	 * and overwrite it to test different failure conditions on
	 * xlat_arch_setup_mmu_cfg():
	 *
	 *	- Call xlat_arch_setup_mmu_cfg() with an uninitialized
	 *	  context configuration.
	 *	- Call xlat_arch_setup_mmu_cfg() for a CPU which
	 *	  does not have support for 4KB granularity.
	 *	- Call xlat_arch_setup_mmu_cfg() for a CPU which
	 *	  does not support FEAT_LPA2 but reports a PA
	 *	  size larger than 48 bits.
	 ***************************************************************/

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	/* VA space boundaries */
	start_va = xlat_test_helpers_get_start_va(VA_LOW_REGION, max_va_size);
	end_va = start_va + max_va_size - 1ULL;

	/* Generate only a single mmap region for each region */
	xlat_test_helpers_rand_mmap_array(&init_mmap, 1U, start_va, end_va, true);

	retval = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &init_mmap,
					1U, max_va_size);
	CHECK_TRUE(retval == 0);

	retval = xlat_ctx_init(&ctx, &cfg, &tbls,
			       xlat_test_helpers_tbls(),
			       XLAT_TESTS_MAX_TABLES);
	CHECK_TRUE(retval == 0);

	/* Force the context to be uninitialized */
	ctx.cfg->initialized = false;

	/* Try to initialize MMU for the given context */
	retval = xlat_arch_setup_mmu_cfg(&ctx, &mmu_config);

	/* Verify that the MMU has failed to be initialized */
	CHECK_TRUE(retval == -EINVAL);

	/* Restore the context initialized flag */
	ctx.cfg->initialized = true;

	/* Force the architecture to report 4K granularity as not available */
	host_write_sysreg("id_aa64mmfr0_el1",
		INPLACE(ID_AA64MMFR0_EL1_PARANGE, 5U) |
		INPLACE(ID_AA64MMFR0_EL1_TGRAN4,
				ID_AA64MMFR0_EL1_TGRAN4_NOT_SUPPORTED));

	/* Try to initialize MMU for the given context */
	retval = xlat_arch_setup_mmu_cfg(&ctx, &mmu_config);

	/* Verify that the MMU has failed to be initialized */
	CHECK_TRUE(retval == -EPERM);

	/*
	 * Force the architecture to report 4K granularity available without
	 * support for LPA2 but with an PA size of more than 48 bits.
	 * Note that this scenario should never happen on the architecture
	 * however, the library still checks for this.
	 */
	host_write_sysreg("id_aa64mmfr0_el1",
		INPLACE(ID_AA64MMFR0_EL1_PARANGE, 6U) |
		INPLACE(ID_AA64MMFR0_EL1_TGRAN4,
				ID_AA64MMFR0_EL1_TGRAN4_SUPPORTED));

	/* Try to initialize MMU for the given context */
	retval = xlat_arch_setup_mmu_cfg(&ctx, &mmu_config);

	/* Verify that the MMU has failed to be initialized */
	CHECK_TRUE(retval == -EPERM);

}

void xlat_arch_setup_mmu_cfg_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Test xlat_arch_setup_mmu_cfg() with a NULL context.
	 ***************************************************************/

	struct xlat_mmu_cfg mmu_config;

	test_helpers_expect_assert_fail(true);
	(void)xlat_arch_setup_mmu_cfg(NULL, &mmu_config);
	test_helpers_fail_if_no_assert_failed();
}

void xlat_arch_setup_mmu_cfg_tc4(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region init_mmap;

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Test xlat_arch_setup_mmu_cfg() with a context in which the
	 * configuration is NULL.
	 *
	 * This test reuses xlat_get_llt_from_va_prepare_assertion()
	 * in order to generate an initial valid context.
	 ***************************************************************/

	struct xlat_mmu_cfg mmu_config;

	xlat_get_llt_from_va_prepare_assertion(&ctx, &cfg, &tbls, &init_mmap);

	/* Force the context configuration to NULL */
	ctx.cfg = NULL;

	test_helpers_expect_assert_fail(true);
	(void)xlat_arch_setup_mmu_cfg(&ctx, &mmu_config);
	test_helpers_fail_if_no_assert_failed();
}

void xlat_arch_setup_mmu_cfg_tc5(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	struct xlat_mmap_region init_mmap;

	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Test xlat_arch_setup_mmu_cfg() with a context in which the
	 * 'tbls' structure is NULL.
	 *
	 * This test reuses xlat_get_llt_from_va_prepare_assertion()
	 * in order to generate an initial valid context.
	 ***************************************************************/

	struct xlat_mmu_cfg mmu_config;

	xlat_get_llt_from_va_prepare_assertion(&ctx, &cfg, &tbls, &init_mmap);

	/* Force the context tables structure to NULL */
	ctx.tbls = NULL;

	test_helpers_expect_assert_fail(true);
	(void)xlat_arch_setup_mmu_cfg(&ctx, &mmu_config);
	test_helpers_fail_if_no_assert_failed();
}

void xlat_arch_setup_mmu_cfg_tc6(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, end_va;
	int retval;
	struct xlat_mmap_region init_mmap;
	uint64_t max_va_size =	XLAT_TEST_MAX_VA_SIZE();
	struct xlat_mmu_cfg mmu_config;

	/***************************************************************
	 * TEST CASE 6:
	 * Generate a valid translation context for one of the regions
	 * and call xlat_arch_setup_mmu_cfg() with the MMU enabled.
	 *
	 ***************************************************************/

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

	/* VA space boundaries */
	start_va = xlat_test_helpers_get_start_va(VA_LOW_REGION, max_va_size);
	end_va = start_va + max_va_size - 1UL;

	/* Generate only a single mmap region for each region */
	xlat_test_helpers_rand_mmap_array(&init_mmap, 1U, start_va, end_va, true);

	retval = xlat_ctx_cfg_init(&cfg, VA_LOW_REGION, &init_mmap,
					1U, max_va_size);
	CHECK_TRUE(retval == 0);

	retval = xlat_ctx_init(&ctx, &cfg, &tbls,
				xlat_test_helpers_tbls(),
				XLAT_TESTS_MAX_TABLES);
	CHECK_TRUE(retval == 0);

	/* Force the MMU enablement */
	xlat_enable_mmu_el2();

	test_helpers_expect_assert_fail(true);

	/* Initialize MMU config for the given context */
	retval = xlat_arch_setup_mmu_cfg(&ctx, &mmu_config);
	CHECK_TRUE(retval == 0);

	/* Try to write the MMU config for the given context */
	xlat_arch_write_mmu_cfg(&mmu_config);

	test_helpers_fail_if_no_assert_failed();
}

void xlat_arch_setup_mmu_cfg_tc7(void)
{
	/***************************************************************
	 * TEST CASE 7:
	 *
	 * Test xlat_arch_setup_mmu_cfg() with a NULL config.
	 ***************************************************************/

	struct xlat_ctx ctx;

	test_helpers_expect_assert_fail(true);
	(void)xlat_arch_setup_mmu_cfg(&ctx, NULL);
	test_helpers_fail_if_no_assert_failed();
}

void xlat_get_oa_from_tte_tc1(void)
{
	uint64_t test_tte, val_addr, output_addr;

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Test xlat_get_oa_from_tte() with 4K granularity and with and
	 * without LPA2 support.
	 ***************************************************************/

	/*
	 * Generate a random TTE to test. We are not concerned about the
	 * validity of the TTE or about any bitfield that is not part of
	 * the output address, as xlat_get_oa_from_tte() is expected to
	 * just ignore those.
	 */
	test_tte = ~0ULL;

	/* Test with FEAT_LPA2 available */
	host_write_sysreg("id_aa64mmfr0_el1",
				INPLACE(ID_AA64MMFR0_EL1_PARANGE, 6UL) |
				INPLACE(ID_AA64MMFR0_EL1_TGRAN4,
					ID_AA64MMFR0_EL1_TGRAN4_LPA2));

	/* Generate the validation address from the test TTE */
	val_addr = test_tte & BIT_MASK_ULL(TTE_OA_BIT_49_LPA2, OA_SHIFT);
	val_addr |= INPLACE(OA_BITS_50_51, EXTRACT(TTE_OA_BITS_50_51, test_tte));

	output_addr = xlat_get_oa_from_tte(test_tte);

	CHECK_VERBOSE((val_addr == output_addr),
		      "Test xlat_get_oa_from_tte, LPA2 supported: OA = %p - Expected = %p",
		      (void *)output_addr, (void *)val_addr);

	/* Repeat the test, by disabling support for FEAT_LPA2 this time */
	host_write_sysreg("id_aa64mmfr0_el1",
		INPLACE(ID_AA64MMFR0_EL1_PARANGE, 5U) |
		INPLACE(ID_AA64MMFR0_EL1_TGRAN4,
				ID_AA64MMFR0_EL1_TGRAN4_SUPPORTED));

	/* Generate the validation address */
	val_addr = test_tte & BIT_MASK_ULL(TTE_OA_MSB, OA_SHIFT);

	output_addr = xlat_get_oa_from_tte(test_tte);

	CHECK_VERBOSE((val_addr == output_addr),
		      "Test xlat_get_oa_from_tte, LPA2 not supported: OA = %p - Expected = %p",
		      (void *)output_addr, (void *)val_addr);
}

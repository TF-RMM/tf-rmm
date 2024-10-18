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
#include <xlat_tables.h>	/* API to test */
#include <xlat_test_defs.h>
#include <xlat_test_helpers.h>
}

/*
 * Helper function to shuffle the content of a buffer
 * with a given stride.
 *
 * This function performs very basic randomization for the
 * shuffle.
 */
static void buffer_shuffle(unsigned char *buf, size_t size, unsigned int stride)
{

/* Maximum stride allowed */
#define MAX_STRIDE	(128U)

	unsigned long items = size / stride;
	unsigned int index_i, index_j;
	unsigned char tmp_buf[MAX_STRIDE];

	assert(stride <= MAX_STRIDE);

	if (items > 1U) {
		for (unsigned int i = 0U; i <= items; i++) {

			/* Shuffle random indexes */
			do {
				index_i =
				(unsigned int)test_helpers_get_rand_in_range(0UL, items - 1);
				index_j =
				(unsigned int)test_helpers_get_rand_in_range(0UL, items - 1);
			} while (index_i == index_j);

			memcpy((void *)&tmp_buf[0],
			       (void *)&buf[stride * index_i],
			       (size_t)stride);
			memcpy((void *)&buf[stride * index_i],
			       (void *)&buf[stride * index_j],
			       (size_t)stride);
			memcpy((void *)&buf[stride * index_j],
			       (void *)&tmp_buf[0],
			       (size_t)stride);
		}
	}
}

/*
 * Helper function to initialize and setup all the data
 * structures used for xlat_ctx_cfg_init(). This function initializes the
 * context with a validaton mmap array containing the expected values after
 * xlat_ctx_cfg_init() has been called to initialize the context and generates
 * an mmap array to be used for the xlat_ctx_cfg_init() invocation.
 */
static void xlat_test_cfg_init_setup(struct xlat_ctx_cfg *cfg,
				     struct xlat_mmap_region *init_mmap,
				     struct xlat_mmap_region *val_mmap,
				     unsigned int mmaps,
				     size_t va_size,
				     xlat_addr_region_id_t region,
				     bool allow_transient)
{
	uintptr_t start_va, end_va;
	uintptr_t max_mapped_va_offset, max_mapped_pa;

	/* Clean the data structures */
	memset((void *)cfg, 0, sizeof(struct xlat_ctx_cfg));
	memset((void *)val_mmap, 0, sizeof(struct xlat_mmap_region) * mmaps);
	memset((void *)init_mmap, 0, sizeof(struct xlat_mmap_region) * mmaps);

	/* Calculate VA boundaries for the region */
	start_va = xlat_test_helpers_get_start_va(region, va_size);
	end_va = start_va + va_size - 1ULL;

	/*
	 * Generate a validation mmap array with random boundaries.
	 * The array will be sorted in ascending order of VA, as expected
	 * by xlat_ctx_cfg_init().
	 */
	xlat_test_helpers_rand_mmap_array(&val_mmap[0], mmaps,
					  start_va, end_va, allow_transient);

	/*
	 * Copy the validation memory regions array into the init one, so the
	 * latter can be used to initialize xlat_ctx_cfg_init() and the former
	 * to validate the result if needed.
	 */
	memcpy((void *)init_mmap, (void *)val_mmap,
		sizeof(struct xlat_mmap_region) * mmaps);

	/*
	 * xlat_ctx_cfg_init() adjusts the VA base of the mmap region passed
	 * by subtracting the base VA, so all the VAs will be on the same range
	 * regardless of the memory region where they belong. This helps to
	 * simplify the xlat tables creation.
	 */
	for (unsigned int i = 0U; i < mmaps; i++) {
		val_mmap[i].base_va -= start_va;
	}

	/* The maximum mapped va offset can never go beyond the VA size */
	max_mapped_va_offset = (val_mmap[mmaps - 1U].base_va +
				val_mmap[mmaps - 1U].size - 1U) &
					XLAT_TESTS_LOW_REGION_MASK;

	max_mapped_pa = val_mmap[mmaps - 1U].base_pa +
			val_mmap[mmaps - 1U].size - 1U;

	/* Initialize the xlat_ctx_cfg structure */
	xlat_test_helpers_init_ctx_cfg(cfg, va_size, start_va,
				       max_mapped_pa, max_mapped_va_offset,
				       GET_XLAT_TABLE_LEVEL_BASE(va_size),
				       region, init_mmap, mmaps, true);
}

void map_region_full_spec_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Instantiate a struct xlat_mmap_region structure and populate
	 * it using MAP_REGION_FULL_SPEC macro. Verify that the
	 * structure fields are right.
	 ***************************************************************/
	struct xlat_mmap_region validation_mmap = {
		.base_pa = (uintptr_t)rand(),
		.base_va = (uintptr_t)rand(),
		.size = (size_t)rand(),
		.attr = (uint64_t)rand(),
		.granularity = (size_t)rand()
	};

	struct xlat_mmap_region test_mmap = MAP_REGION_FULL_SPEC(
		validation_mmap.base_pa,
		validation_mmap.base_va,
		validation_mmap.size,
		validation_mmap.attr,
		validation_mmap.granularity
	);

	CHECK_TRUE(XLAT_TEST_XLAT_MMAP_REGION_CMP(validation_mmap,
						  test_mmap));
}

void map_region_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Instantiate a struct xlat_mmap_region structure and populate
	 * it using MAP_REGION macro. Verify that the structure fields
	 * are right.
	 ***************************************************************/

	struct xlat_mmap_region validation_mmap = {
		.base_pa = (uintptr_t)rand(),
		.base_va = (uintptr_t)rand(),
		.size = (size_t)rand(),
		.attr = (uint64_t)rand(),
		.granularity = XLAT_TESTS_MAX_BLOCK_SIZE
	};

	/*
	 * Test structure. Fill it using the validation structure
	 * through MAP_REGION macro.
	 */
	struct xlat_mmap_region test_mmap = MAP_REGION(
		validation_mmap.base_pa,
		validation_mmap.base_va,
		validation_mmap.size,
		validation_mmap.attr
	);

	CHECK_TRUE(XLAT_TEST_XLAT_MMAP_REGION_CMP(validation_mmap,
						  test_mmap));
}

void map_region_flat_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Instantiate a struct xlat_mmap_region structure and populate
	 * it using MAP_REGION_FLAT macro. Verify that the structure
	 * fields are right.
	 ***************************************************************/

	/* Validation structure. Fill it with random data */
	uintptr_t base_addr = rand();

	struct xlat_mmap_region validation_mmap = {
		.base_pa = base_addr,
		.base_va = base_addr,
		.size = (size_t)rand(),
		.attr = (uint64_t)rand(),
		.granularity = XLAT_TESTS_MAX_BLOCK_SIZE
	};

	/*
	 * Test structure. Fill it using the validation structure
	 * through MAP_REGION_FLAT macro.
	 */
	struct xlat_mmap_region test_mmap = MAP_REGION_FLAT(
		base_addr,
		validation_mmap.size,
		validation_mmap.attr
	);

	CHECK_TRUE(XLAT_TEST_XLAT_MMAP_REGION_CMP(validation_mmap,
						  test_mmap));
}

void map_region_transient_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Instantiate a struct xlat_mmap_region structure and populate
	 * it using MAP_REGION_TRANSIENT macro. Verify that the
	 * structure fields are right.
	 ***************************************************************/

	/* Validation structure. Fill it with random data */
	struct xlat_mmap_region validation_mmap = {
		/* XLAT_MAP_REGION_TRANSIENT sets base_pa to 0 */
		.base_pa = 0ULL,
		.base_va = (uintptr_t)rand(),
		.size = (size_t)rand(),

		/*
		 * XLAT_MAP_REGION_TRANSIENT sets attr to
		 * MT_TRANSIENT
		 */
		.attr = MT_TRANSIENT,
		.granularity = (size_t)rand()
	};

	/*
	 * Test structure. Fill it using the validation structure
	 * through MAP_REGION_TRANSIENT macro.
	 */
	struct xlat_mmap_region test_mmap = MAP_REGION_TRANSIENT(
		validation_mmap.base_va,
		validation_mmap.size,
		validation_mmap.granularity
	);

	CHECK_TRUE(XLAT_TEST_XLAT_MMAP_REGION_CMP(validation_mmap,
						  test_mmap));
}

void xlat_ctx_cfg_init_tc1(void)
{
	struct xlat_ctx_cfg expected_cfg, test_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Initialize a xlat_ctx_cfg structure with random data through
	 * xlat_ctx_cfg_init(). Then verify that the initialization
	 * was as expected.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&expected_cfg, &init_mmap[0],
					 &val_mmap[0], XLAT_TESTS_MAX_MMAPS,
					 max_va_size, region, true);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == 0);

		/*
		 * Verify that the memory regions array used with
		 * xlat_ctx_cfg_init() has been properly normalized.
		 */
		MEMCMP_EQUAL((void *)&val_mmap[0], (void *)&init_mmap[0],
		     sizeof(struct xlat_mmap_region) * XLAT_TESTS_MAX_MMAPS);

		/*
		 * Test that the xlat_ctx_cfg structure is
		 * properly initialized.
		 */
		MEMCMP_EQUAL((void *)&expected_cfg, (void *)&test_cfg,
			     sizeof(struct xlat_ctx_cfg));
	}
}

void xlat_ctx_cfg_init_tc2(void)
{
	struct xlat_ctx_cfg foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Try to initialize a NULL xlat_ctx_cfg structure.
	 * All the rest of parameters will be valid.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					 XLAT_TESTS_MAX_MMAPS,
					 max_va_size,
					 region, true);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(NULL, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

void xlat_ctx_cfg_init_tc3(void)
{
	struct xlat_ctx_cfg test_cfg;
	xlat_addr_region_id_t region;
	int retval;

	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with a NULL list
	 * of mmap regions.
	 * All the rest of parameters will be valid.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, NULL,
					   XLAT_TESTS_MAX_MMAPS,
					   XLAT_TEST_MAX_VA_SIZE());

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

void xlat_ctx_cfg_init_tc4(void)
{
	struct xlat_ctx_cfg foo_cfg, test_cfg;
	struct xlat_mmap_region test_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t mmap_region, cfg_region;
	int retval;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with random data
	 * where the xlat_addr_region_id_t does not match the mmap
	 * regions.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		mmap_region = (xlat_addr_region_id_t)i;
		cfg_region = (xlat_addr_region_id_t)((i + 1U) % VA_REGIONS);

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &test_mmap[0],
				XLAT_TESTS_MAX_MMAPS, max_va_size,
				mmap_region, true);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, cfg_region,
					   &init_mmap[0], XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

void xlat_ctx_cfg_init_tc5(void)
{
	struct xlat_ctx_cfg test_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;

	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with an empty mmap
	 * region array.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&init_mmap[0], 0,
			sizeof(xlat_mmap_region) * XLAT_TESTS_MAX_MMAPS);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0], 0U,
				XLAT_TEST_MAX_VA_SIZE());

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

void xlat_ctx_cfg_init_tc6(void)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;
	size_t test_va_size, va_size;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with a set of
	 * invalid VA space sizes:
	 *	- A misaligned VA space size.
	 *	- A VA space size larger than the maximum permitted.
	 *	- A VA space size lower than the minimum permitted.
	 *
	 * The rest of the arguments to xlat_ctx_cfg_init() are as
	 * expected.
	 ***************************************************************/
	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/*
		 * Get a VA large enough for testing but leaving some room
		 * for it to grow without being larger than the maximum
		 * allowed.
		 */
		va_size = max_va_size - PAGE_SIZE;

		/* Add a random offset to it to misalign */
		test_va_size = va_size + test_helpers_get_rand_in_range(1UL,
								PAGE_SIZE - 1);

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					va_size, region, true);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   test_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Test with a VA Size larger than the max permitted */
		test_va_size = max_va_size + PAGE_SIZE;

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   test_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Test with a VA Size lower than the minimum permitted */
		test_va_size = MIN_VIRT_ADDR_SPACE_SIZE - PAGE_SIZE;

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   test_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

void xlat_ctx_cfg_init_tc7(void)
{
	struct xlat_ctx_cfg test_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/******************************************************************
	 * TEST CASE 7:
	 *
	 * Try to initialize an already initialized xlat_ctx_cfg structure
	 *****************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/*
		 * Initialize the test structures with the expected.
		 * test_cfg will be marked as initialized.
		 */
		xlat_test_cfg_init_setup(&test_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					max_va_size, region, true);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EALREADY);
	}
}

void xlat_ctx_cfg_init_tc8(void)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t region;
	unsigned int mmap_index;
	int retval;
	unsigned int index;
	uint64_t id_aa64mmfr0_el1 = read_id_aa64mmfr0_el1();
	bool lpa2 = is_feat_lpa2_4k_present();
	unsigned int pa_range_bits_arr[] = {
		PARANGE_0000_WIDTH, PARANGE_0001_WIDTH, PARANGE_0010_WIDTH,
		PARANGE_0011_WIDTH, PARANGE_0100_WIDTH, PARANGE_0101_WIDTH,
		PARANGE_0110_WIDTH
	};
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 8:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with mmap areas
	 * in which the PA have different configurations
	 *
	 *	- 'base_pa' > maximum supported PA
	 *	- 'base_pa' < maximum supported PA && 'base_pa' + 'size'
	 *	  > maximum supported PA
	 *	- PAs on different memory regions overlap.
	 *	- Some memory regions have misaligned PAs.
	 ***************************************************************/

	index = ARRAY_SIZE(pa_range_bits_arr);
	index = (lpa2 == true) ? index : index - 1U;
	index = (unsigned int)test_helpers_get_rand_in_range(0UL, index - 1U);

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Configure a random maximum PA supported */
		xlat_test_helpers_set_parange(index);

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					max_va_size, region, false);

		/*
		 * Create a backup copy of the current mmap regions.
		 * Use 'val_mmap' for that.
		 */
		(void)memcpy(&val_mmap[0], &init_mmap[0],
			sizeof(struct xlat_mmap_region) * XLAT_TESTS_MAX_MMAPS);

		/*
		 * Overwrite the PA of the last memory map region to
		 * be higher than the maximum PA supported.
		 *
		 * This tests for the case in which
		 * 'base_pa' > maximum allowed.
		 */
		init_mmap[XLAT_TESTS_MAX_MMAPS - 1U].base_pa =
					1ULL << pa_range_bits_arr[index];

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -ERANGE);

		/* Restore init_mmap for the next test */
		(void)memcpy(&init_mmap[0], &val_mmap[0],
			sizeof(struct xlat_mmap_region) * XLAT_TESTS_MAX_MMAPS);

		/*
		 * Now test the case in which 'base_pa' < maximum PA
		 * but 'base_pa' + 'size' > maximum PA.
		 *
		 * Configure the last mmap region with a 'base_pa'
		 * such as 'base_pa' + 'size' is above the maximum PA but
		 * 'base_va' + 'size' is within the valid range.
		 *
		 * Note that 'size' will be at least the size of a memory page.
		 */
		init_mmap[XLAT_TESTS_MAX_MMAPS - 1U].base_pa =
					(1ULL << pa_range_bits_arr[index]) -
					PAGE_SIZE;

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -ERANGE);

		/* Restore id_aa64mmfr0_el1 for the next test */
		host_write_sysreg("id_aa64mmfr0_el1", id_aa64mmfr0_el1);

		/* Restore init_mmap for the next test */
		(void)memcpy(&init_mmap[0], &val_mmap[0],
			sizeof(struct xlat_mmap_region) * XLAT_TESTS_MAX_MMAPS);

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/*
		 * Overwrite the mmap structures to make the PAs overlap for
		 * the next test
		 */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(1UL,
						XLAT_TESTS_MAX_MMAPS - 1);
		/*
		 * The base_pa of mmap entry at 'mmap_index' is adjusted to an
		 * offset of 'PAGE_SIZE' of previous entry
		 * ('base_pa' is set to the same value as 'base_va').
		 * Each entry has a size of at least 2 pages, so the PA of the
		 * regions will overlap.
		 */
		init_mmap[mmap_index].base_pa =
			init_mmap[mmap_index - 1U].base_pa + PAGE_SIZE;

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EPERM);

		/* Restore init_mmap for the next test */
		(void)memcpy(&init_mmap[0], &val_mmap[0],
			sizeof(struct xlat_mmap_region) * XLAT_TESTS_MAX_MMAPS);

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/*
		 * Overwrite the PA on one of the memory map regions to
		 * make it misaligned.
		 */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(0UL,
				(unsigned long)(XLAT_TESTS_MAX_MMAPS - 1));
		init_mmap[mmap_index].base_pa +=
				test_helpers_get_rand_in_range(1UL,
								PAGE_SIZE - 1);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EFAULT);
	}
}

void xlat_ctx_cfg_init_tc9(void)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t region;
	unsigned int mmap_index;
	int retval;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 9:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with mmap areas
	 * in which the VA have different configurations:
	 *
	 *	- Memory map regions have misaligned VAs.
	 *	- Memory map regions have overlapping VAs.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					max_va_size, region, true);

		/*
		 * Craeate a backup copy of the current mmap regions.
		 * Use 'val_mmap' for that.
		 */
		(void)memcpy(&val_mmap[0], &init_mmap[0],
			sizeof(struct xlat_mmap_region) * XLAT_TESTS_MAX_MMAPS);

		/*
		 * Overwrite the VA on one of the memory map regions to
		 * make it misaligned.
		 */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(0UL,
				(unsigned long)(XLAT_TESTS_MAX_MMAPS - 1));
		init_mmap[mmap_index].base_va +=
				test_helpers_get_rand_in_range(1UL,
								PAGE_SIZE - 1);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EFAULT);

		/* Restore init_mmap for the next test */
		(void)memcpy(&init_mmap[0], &val_mmap[0],
			sizeof(struct xlat_mmap_region) * XLAT_TESTS_MAX_MMAPS);

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Overwrite the mmap structures to make the VAs overlap */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(1UL,
						XLAT_TESTS_MAX_MMAPS - 1);
		/*
		 * The base_va of mmap entry at 'mmap_index' is adjusted to an
		 * offset of 'PAGE_SIZE' of previous entry.
		 * Each entry has a size of at least 2 pages, so the regions
		 * will overlap whilst keeping in ascending order of VA.
		 */
		init_mmap[mmap_index].base_va =
			init_mmap[mmap_index - 1U].base_va +
					 PAGE_SIZE;

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EPERM);
	}
}

void xlat_ctx_cfg_init_tc10(void)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t region;
	unsigned int mmap_index;
	int retval;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 10:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with mmap areas
	 * in which the size is misaligned.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					max_va_size, region, true);

		/*
		 * Overwrite the size on one of the memory map regions to
		 * make it misaligned.
		 */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(0UL,
				(unsigned long)(XLAT_TESTS_MAX_MMAPS - 1));
		init_mmap[mmap_index].size -= test_helpers_get_rand_in_range(1UL,
								PAGE_SIZE - 1);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EFAULT);
	}
}

void xlat_ctx_cfg_init_tc11(void)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t region;
	unsigned int mmap_index;
	int retval;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 11:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with repeated
	 * memory mapping areas.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					max_va_size, region, true);

		/*
		 * Overwrite a memory mapping region to make it a duplicate
		 * of the previous one.
		 */
		mmap_index = (unsigned int)test_helpers_get_rand_in_range(1UL,
						XLAT_TESTS_MAX_MMAPS - 1);
		memcpy((void *)&init_mmap[mmap_index],
		       (void *)&init_mmap[mmap_index - 1U],
		       sizeof(struct xlat_mmap_region));

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EPERM);
	}
}

void xlat_ctx_cfg_init_tc12(void)
{
	struct xlat_ctx_cfg test_cfg, foo_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 12:
	 *
	 * Try to initialize a xlat_ctx_cfg structure with out of order
	 * memory mapping areas.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&foo_cfg, &init_mmap[0], &val_mmap[0],
					XLAT_TESTS_MAX_MMAPS,
					max_va_size, region, true);

		/* Randomly shuffle the memory mapping areas */
		buffer_shuffle((unsigned char *)&init_mmap[0],
				sizeof(struct xlat_mmap_region) *
						XLAT_TESTS_MAX_MMAPS,
				sizeof(struct xlat_mmap_region));

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EPERM);
	}
}

void xlat_ctx_cfg_init_tc13(void)
{
	struct xlat_ctx_cfg expected_cfg, test_cfg;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	struct xlat_mmap_region val_mmap[XLAT_TESTS_MAX_MMAPS];
	xlat_addr_region_id_t region;
	int retval;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 13:
	 *
	 * Running without support for FEAT_LPA2, initialize a
	 * xlat_ctx_cfg structure with random data through
	 * xlat_ctx_cfg_init() but forcing to use a granularity for
	 * level -1 (only supported for FEAT_LPA2). Then verify that the
	 * initialization fails as expected.
	 *
	 * Note: This test is only supported for non-LPA2 runs.
	 ***************************************************************/

	/* Ensure FEAT_LPA2 is not supported */
	CHECK_FALSE(is_feat_lpa2_4k_present());

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&test_cfg, 0, sizeof(struct xlat_ctx_cfg));

		/* Initialize the test structures with the expected values */
		xlat_test_cfg_init_setup(&expected_cfg, &init_mmap[0],
					 &val_mmap[0], XLAT_TESTS_MAX_MMAPS,
					 max_va_size, region, true);

		/* Force an incorrect granularity */
		init_mmap[0].granularity = XLAT_BLOCK_SIZE(-1);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&test_cfg, region, &init_mmap[0],
					   1U, max_va_size);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

void xlat_ctx_init_tc1(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg, val_cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, end_va;
	xlat_addr_region_id_t region;
	int retval;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Initialize a context with a number of valid random
	 * memory mapping areas and generate the corresponding
	 * translation tables.
	 * Verify that the return code from xlat_ctx_init() is as
	 * expected and the context is properly generated.
	 * This test does not perform any check on the translation
	 * tables themselves.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* VA space boundaries */
		start_va = xlat_test_helpers_get_start_va(region, max_va_size);
		end_va = start_va + max_va_size - 1ULL;

		xlat_test_helpers_rand_mmap_array(&init_mmap[0],
				XLAT_TESTS_MAX_MMAPS, start_va, end_va, true);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify that the context cfg is properly created */
		CHECK_TRUE(retval == 0);

		memcpy((void *)&val_cfg, (void *)&cfg,
			sizeof(struct xlat_ctx_cfg));

		/* Test xlat_ctx_init() */
		retval = xlat_ctx_init(&ctx, &cfg, &tbls,
				       xlat_test_helpers_tbls(),
				       XLAT_TESTS_MAX_TABLES);

		/* Verify the result */
		CHECK_TRUE(retval == 0);

		/* Validate that the configuration has not been altered */
		MEMCMP_EQUAL((void *)&val_cfg, (void *)&cfg,
			     sizeof(struct xlat_ctx_cfg));

		/* Validate the xlat_ctx structure */
		CHECK_TRUE(ctx.cfg == &cfg);
		CHECK_TRUE(ctx.tbls == &tbls);

		/*
		 * Validate the xlat_ctx_tbls structure.
		 *
		 * NOTE: As the memory regions are random, the `next_table`
		 * field is not validated here. Instead, it will be validated
		 * for each especific test later.
		 */
		CHECK_TRUE(tbls.initialized == true);
		CHECK_TRUE(tbls.tables == xlat_test_helpers_tbls());
		CHECK_TRUE(tbls.tables_num == XLAT_TESTS_MAX_TABLES);
	}
}

void xlat_ctx_init_tc2(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	int retval;

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Try to initialize a context with a
	 *	- NULL configuration.
	 *	- Invalid configuration.
	 ***************************************************************/

	/* Clean the data structures */
	memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
	memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));
	memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));

	/* Test xlat_ctx_init() with NULL configuration */
	retval = xlat_ctx_init(&ctx, NULL, &tbls, xlat_test_helpers_tbls(),
				XLAT_TESTS_MAX_TABLES);

	/* Verify the result */
	CHECK_TRUE(retval == -EINVAL);

	/* Test xlat_ctx_init() with invalid configuration */
	retval = xlat_ctx_init(&ctx, &cfg, &tbls, xlat_test_helpers_tbls(),
				XLAT_TESTS_MAX_TABLES);

	/* Verify the result */
	CHECK_TRUE(retval == -EINVAL);
}

void xlat_ctx_init_tc3(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, end_va;
	xlat_addr_region_id_t region;
	uint64_t *xlat_tables;
	unsigned int offset;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	int retval;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try to initialize a context with
	 *	- A NULL set of translation tables
	 *	- A NULL xlat_ctx_tbls structure
	 *	- A NULL xlat_ctx structure
	 *	- A set of misaligned translation tables
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* VA space boundaries */
		start_va = xlat_test_helpers_get_start_va(region, max_va_size);
		end_va = start_va + max_va_size - 1ULL;

		xlat_test_helpers_rand_mmap_array(&init_mmap[0],
				XLAT_TESTS_MAX_MMAPS, start_va, end_va, true);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify that the context cfg is properly created */
		CHECK_TRUE(retval == 0);

		/* Test xlat_ctx_init() with a NULL set of tables */
		retval = xlat_ctx_init(&ctx, &cfg, &tbls, NULL,
					XLAT_TESTS_MAX_TABLES);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);

		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* Test xlat_ctx_init() with a NULL xlat_ctx_tbls structure */
		retval = xlat_ctx_init(&ctx, &cfg, NULL,
					xlat_test_helpers_tbls(),
					XLAT_TESTS_MAX_TABLES);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);

		/* Test xlat_ctx_init() with a NULL xlat_ctx structure */
		retval = xlat_ctx_init(NULL, &cfg, &tbls,
					xlat_test_helpers_tbls(),
					XLAT_TESTS_MAX_TABLES);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);

		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/*
		 * Generate a random offset to test a set of
		 * misaligned tables
		 */
		offset = (unsigned int)test_helpers_get_rand_in_range(1UL,
						XLAT_TABLE_ENTRIES - 1);

		/* Test xlat_ctx_init() with a set of misaligned tables */
		xlat_tables = xlat_test_helpers_tbls();
		retval = xlat_ctx_init(&ctx, &cfg, &tbls, &xlat_tables[offset],
					XLAT_TESTS_MAX_TABLES);

		/* Verify the result */
		CHECK_TRUE(retval == -EINVAL);
	}
}

void xlat_ctx_init_tc4(void)
{
	struct xlat_ctx ctx;
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
	uintptr_t start_va, end_va;
	xlat_addr_region_id_t region;
	struct xlat_mmap_region init_mmap[XLAT_TESTS_MAX_MMAPS];
	int retval;
	uint64_t max_va_size = XLAT_TEST_MAX_VA_SIZE();

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Try to initialize a context with a number of valid
	 * random memory mapping areas but an inssuficient number of
	 * available translation tables.
	 *
	 * NOTE: Current implementation of the xlat library asserts
	 *	 when run out of space to allocate new translation
	 *	 tables. Future improvements on the xlat library should
	 *	 just return an error code and exit gracefully upon
	 *	 this condition.
	 ***************************************************************/

	for (unsigned int i = 0U; i < (unsigned int)VA_REGIONS; i++) {
		region = (xlat_addr_region_id_t)i;

		/* Clean the data structures */
		memset((void *)&ctx, 0, sizeof(struct xlat_ctx));
		memset((void *)&cfg, 0, sizeof(struct xlat_ctx_cfg));
		memset((void *)&tbls, 0, sizeof(struct xlat_ctx_tbls));

		/* VA space boundaries */
		start_va = xlat_test_helpers_get_start_va(region, max_va_size);
		end_va = start_va + max_va_size - 1ULL;

		xlat_test_helpers_rand_mmap_array(&init_mmap[0],
				XLAT_TESTS_MAX_MMAPS, start_va, end_va, true);

		/* Initialize the test structure */
		retval = xlat_ctx_cfg_init(&cfg, region, &init_mmap[0],
					   XLAT_TESTS_MAX_MMAPS,
					   max_va_size);

		/* Verify that the context cfg is properly created */
		CHECK_TRUE(retval == 0);

		/* Test xlat_ctx_init() */
		test_helpers_expect_assert_fail(true);
		retval = xlat_ctx_init(&ctx, &cfg, &tbls,
				       xlat_test_helpers_tbls(), 1U);
		test_helpers_fail_if_no_assert_failed();
	}
}

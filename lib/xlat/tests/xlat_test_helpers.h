/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef XLAT_TEST_HELPERS_H
#define XLAT_TEST_HELPERS_H

#include <arch_helpers.h>
#include <xlat_contexts.h>
#include <xlat_defs.h>

/* Maximum number of tables to use for tests */
#define XLAT_TESTS_MAX_TABLES	(20U)

/* Maximum number of mmap regions to use for tests */
#define XLAT_TESTS_MAX_MMAPS	(20U)

/* Macros to specify LPA2 status */
#define LPA2_ENABLED		(true)
#define LPA2_DISABLED		(false)

/*
 * Return the minimum lookup level supported.
 */
#define XLAT_TEST_MIN_LVL()			\
	((is_feat_lpa2_4k_present() == true) ?	\
	XLAT_TABLE_LEVEL_MIN : XLAT_TABLE_LEVEL_MIN + 1)

/*
 * Return the maximum VA space size.
 */
#define XLAT_TEST_MAX_VA_SIZE()			\
	((is_feat_lpa2_4k_present() == true) ?	\
	MAX_VIRT_ADDR_SPACE_SIZE_LPA2 : MAX_VIRT_ADDR_SPACE_SIZE)

/*
 * Return the PA Mask
 */
#define XLAT_TEST_GET_PA_MASK()			\
	((is_feat_lpa2_4k_present() == true) ?	\
	XLAT_TESTS_PA_MASK_LPA2 : XLAT_TESTS_PA_MASK)


/*
 * Compare two xlat_mmap_region structures
 */
#define XLAT_TEST_XLAT_MMAP_REGION_CMP(_a, _b)	\
	(((_a).base_pa == (_b).base_pa) &&		\
	 ((_a).base_va == (_b).base_va) &&		\
	 ((_a).size == (_b).size) &&		\
	 ((_a).attr == (_b).attr) &&		\
	 ((_a).granularity == (_b).granularity))

/*
 * Helper function to initialize a xlat_ctx_tbls structure with
 * a given set of parameters.
 *
 * Note that this function expects valid ranges, so no checks
 * are done on any of the arguments.
 */
void xlat_test_helpers_init_ctx_tbls(struct xlat_ctx_tbls *ctx_tbls,
				     uint64_t *tbls,
				     unsigned int tables_num,
				     unsigned int next_table,
				     bool initialized);

/*
 * Helper function to initialize a xlat_ctx_cfg structure with
 * a given set of parameters.
 *
 * Note that this function expects valid ranges, so no checks
 * are done on any of the arguments.
 */
void xlat_test_helpers_init_ctx_cfg(struct xlat_ctx_cfg *ctx_cfg,
				    uintptr_t max_va_size,
				    uintptr_t base_va,
				    uintptr_t max_mapped_pa,
				    uintptr_t max_mapped_va_offset,
				    int base_level,
				    xlat_addr_region_id_t region,
				    struct xlat_mmap_region *mm,
				    unsigned int mmaps,
				    bool initialized);

/*
 * Helper function to initialize a xlat_ctx structure with
 * a given set of parameters.
 *
 * Note that this function expects valid ranges, so no checks
 * are done on any of the arguments.
 */
void xlat_test_helpers_init_ctx(struct xlat_ctx *ctx,
				struct xlat_ctx_cfg *cfg,
				struct xlat_ctx_tbls *tbls);

/* Helper function to return a random set of attributes for a mmap region */
uint64_t xlat_test_helpers_rand_mmap_attrs(bool allow_transient);

/*
 * Generate a random array of xlat_mmap_region
 * structure ordered by ascending VA.
 */
void xlat_test_helpers_rand_mmap_array(struct xlat_mmap_region *mmap,
					size_t size, uintptr_t min_va,
					uintptr_t max_va,
					bool allow_transient);

/* Return the base VA according to the region */
uintptr_t xlat_test_helpers_get_start_va(xlat_addr_region_id_t region,
					 size_t va_size);

/*
 * Helper function to perform a table walk given a VA.
 * This function returns the tte for the VA, as well as the
 * look-up level, the index of the tte within the block/page
 * and a pointer to the beginning of the last level xlat
 * table.
 */
int xlat_test_helpers_table_walk(struct xlat_ctx *ctx,
				 uint64_t va,
				 uint64_t *tte,
				 uint64_t **table_ptr,
				 int *level,
				 unsigned int *index);

/*
 * Helper function to generate the lower and upper attributes as expected
 * to be in a block/page tte given the `mmap_attrs` field of a mmap region.
 * The generated attributes are returned via the `attrs` parameter.
 *
 * This function returns 0 if the attributes can be generated and a negative
 * error code otherwise.
 */
int xlat_test_helpers_gen_attrs(uint64_t *attrs, uint64_t mmap_attrs);

/*
 * Helper function to get the attributes (lower and upper) corresponding
 * to VA as specified by mmap region array in the translation context.
 *
 * This function returns 0 if the attributes can be generated and a negative
 * error code otherwise.
 *
 * This function assumes that the context is valid and properly initialized.
 */
int xlat_test_helpers_get_attrs_for_va(struct xlat_ctx *ctx,
					uint64_t va,
					uint64_t *attrs);

/*
 * Return a pointer to the memory allocated for the xlat tables.
 */
uint64_t *xlat_test_helpers_tbls(void);

/*
 * Setup the PA range size in ID_AA64MMFR0_EL1.
 * This function does not make any check on the 'parange'
 * argument
 */
void xlat_test_helpers_set_parange(unsigned int parange);

/*
 * Function to setup the environment for the tests specifying
 * whether FEAT_LPA2 is supported or not.
 */
void xlat_test_setup(bool lpa2);

#endif /* XLAT_TEST_HELPERS_H */

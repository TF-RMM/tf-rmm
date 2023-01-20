/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <errno.h>
#include <host_utils.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <xlat_contexts.h>	/* API to test */
#include <xlat_defs.h>
#include <xlat_tables.h>	/* API to test */
#include <xlat_test_defs.h>

void xlat_test_helpers_init_ctx_tbls(struct xlat_ctx_tbls *ctx_tbls,
				     uint64_t *tbls,
				     unsigned int tables_num,
				     unsigned int next_table,
				     bool initialized)
{
	ctx_tbls->tables = tbls;
	ctx_tbls->tables_num = tables_num;
	ctx_tbls->next_table = next_table;
	ctx_tbls->initialized = initialized;
}

void xlat_test_helpers_init_ctx_cfg(struct xlat_ctx_cfg *ctx_cfg,
				    uintptr_t max_va_size,
				    uintptr_t base_va,
				    uintptr_t max_mapped_pa,
				    uintptr_t max_mapped_va_offset,
				    unsigned int base_level,
				    xlat_addr_region_id_t region,
				    struct xlat_mmap_region *mm,
				    unsigned int mmaps,
				    bool initialized)
{
	ctx_cfg->max_va_size = max_va_size;
	ctx_cfg->mmap = mm;
	ctx_cfg->mmap_regions = mmaps;
	ctx_cfg->base_va = base_va;
	ctx_cfg->max_mapped_pa = max_mapped_pa;
	ctx_cfg->max_mapped_va_offset = max_mapped_va_offset;
	ctx_cfg->base_level = base_level;
	ctx_cfg->region = region;
	ctx_cfg->initialized = initialized;
}

void xlat_test_helpers_init_ctx(struct xlat_ctx *ctx,
				struct xlat_ctx_cfg *cfg,
				struct xlat_ctx_tbls *tbls)
{
	ctx->cfg = cfg;
	ctx->tbls = tbls;
}

void xlat_test_hepers_arch_init(void)
{
	unsigned int retval;

	/* Enable the platform with support for multiple PEs */
	test_helpers_rmm_start(true);

	/*
	 * Reset the sysreg state so that we can setup
	 * custom values for the tests
	 */
	host_util_zero_sysregs_and_cbs();

	/* Setup id_aa64mmfr0_el1 with a PA size of 48 bits */
	retval = host_util_set_default_sysreg_cb("id_aa64mmfr0_el1",
				INPLACE(ID_AA64MMFR0_EL1_PARANGE, 5UL));

	/* Initialize MMU registers to 0 */
	retval = host_util_set_default_sysreg_cb("sctlr_el2", 0UL);
	retval = host_util_set_default_sysreg_cb("mair_el2", 0UL);
	retval = host_util_set_default_sysreg_cb("tcr_el2", 0UL);
	retval = host_util_set_default_sysreg_cb("ttbr0_el2", 0UL);
	retval = host_util_set_default_sysreg_cb("ttbr1_el2", 0UL);

	assert(retval == 0);

	/* Make sure current cpu id is 0 (primary processor) */
	host_util_set_cpuid(0U);

	test_helpers_expect_assert_fail(false);
}

int xlat_test_helpers_table_walk(struct xlat_ctx *ctx,
				 unsigned long long va,
				 uint64_t *tte,
				 uint64_t **table_ptr,
				 unsigned int *level,
				 unsigned int *index)
{
	struct xlat_ctx_cfg *cfg;
	struct xlat_ctx_tbls *tbls;
	uint64_t ctte;
	uint64_t *table;

	assert(ctx != NULL);
	assert(ctx->tbls != NULL);
	assert(ctx->cfg != NULL);
	assert(tte != NULL);
	assert(level != NULL);
	assert(index != NULL);

	cfg = ctx->cfg;
	tbls = ctx->tbls;

	if (tbls->initialized == false) {
		return -EINVAL;
	}

	if (cfg->initialized == false) {
		return -EINVAL;
	}

	if ((tbls->tables == NULL) || (tbls->tables_num == 0U)) {
		return -EINVAL;
	}

	if (va > cfg->base_va + cfg->max_mapped_va_offset) {
		return -ERANGE;
	}

	/* Base table is the first table of the array */
	table = &tbls->tables[0U];
	for (unsigned int i = cfg->base_level;
					i <= XLAT_TABLE_LEVEL_MAX; i++) {
		uint64_t tte_oa;
		unsigned int tindex =
			(unsigned int)(va >> XLAT_ADDR_SHIFT(i)) &
						XLAT_TABLE_ENTRIES_MASK;

		if (tindex >= XLAT_TABLE_ENTRIES) {
			return -ERANGE;
		}

		ctte = table[tindex];
		if (ctte == INVALID_DESC) {
			return -ERANGE;
		}

		if (XLAT_TESTS_IS_TRANSIENT_DESC(ctte)) {
			*tte = ctte;
			*level = i;
			*index = tindex;
			if (table_ptr != NULL) {
				*table_ptr = table;
			}
			return 0;
		}

		switch (i) {
		case 0U:
			/* Only table descriptors allowed here */
			if (!XLAT_TESTS_IS_DESC(ctte, TABLE_DESC)) {
				return -EINVAL;
			}

			if (UPPER_ATTRS(ctte) != 0ULL) {
				/* Table attributes are expected to be 0x0 */
				return -EINVAL;
			}

			tte_oa = EXTRACT(XLAT_TESTS_TBL_ADDR, ctte);
			table = (uint64_t *)tte_oa;
			break;

		case 1U:
		case 2U:
			if (XLAT_TESTS_IS_DESC(ctte, BLOCK_DESC)) {
				*tte = ctte;
				*level = i;
				*index = tindex;
				if (table_ptr != NULL) {
					*table_ptr = table;
				}
				return 0;
			}

			/* This is a table descriptor */
			tte_oa = EXTRACT(XLAT_TESTS_TBL_ADDR, ctte);
			table = (uint64_t *)tte_oa;
			break;

		case 3U:
			/* Only page descriptors allowed here */
			if (!XLAT_TESTS_IS_DESC(ctte, PAGE_DESC)) {
				return -EINVAL;
			}
			*tte = ctte;
			*level = i;
			*index = tindex;
			if (table_ptr != NULL) {
				*table_ptr = table;
			}
			return 0;

		default:
			return -EINVAL;
		}
	}

	/* We should never get here */
	return -EINVAL;
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <cpuid.h>
#include <debug.h>
#include <errno.h>
#include <stdint.h>
#include <utils_def.h>
#include <xlat_contexts.h>
#include <xlat_high_va.h>
#include <xlat_tables.h>

/* Context definition */
static struct xlat_ctx high_va_xlat_ctx[MAX_CPUS];

struct xlat_ctx *xlat_get_high_va_xlat_ctx(void)
{
	return &high_va_xlat_ctx[my_cpuid()];
}

/*
 * Setup xlat table for the high VA region for each PE.
 * Must be called for every PE in the system.
 */
int xlat_high_va_setup(struct xlat_mmap_region *mm, unsigned int regions)
{
	/*
	 * The base tables for all the contexts are manually allocated as a continuous
	 * block of memory (one L3 table per PE).
	 */
	static uint64_t high_va_tts[XLAT_TABLE_ENTRIES * MAX_CPUS] __aligned(XLAT_TABLES_ALIGNMENT);

	unsigned int cpuid = my_cpuid();
	struct xlat_mmu_cfg mmu_config;
	int ret;

	/* Initialize the context configuration for this CPU */
	ret = xlat_ctx_cfg_init(&high_va_xlat_ctx[cpuid], VA_HIGH_REGION,
				 mm, regions, 0UL, XLAT_HIGH_VA_SIZE, RMM_ASID);
	if (!((ret == 0) || (ret == -EALREADY))) {
		return ret;
	}

	/*
	 * Initialize the translation tables for the current context.
	 * This is done on the first boot of each PE.
	 */
	uint64_t *tables_ptr = &high_va_tts[(size_t)XLAT_TABLE_ENTRIES * cpuid];
	ret = xlat_ctx_init(&high_va_xlat_ctx[cpuid],
				tables_ptr, 1U,
				(uint64_t)tables_ptr);

	if (!((ret == 0) || (ret == -EALREADY))) {
		return ret;
	}

	/* Configure MMU registers */
	ret = xlat_arch_setup_mmu_cfg(&high_va_xlat_ctx[cpuid], &mmu_config);

	if (ret == 0) {
		xlat_arch_write_mmu_cfg(&mmu_config);
	}

	return ret;
}

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

#define RMM_SLOT_BUF_SIZE	((XLAT_HIGH_VA_SLOT_NUM) * (GRANULE_SIZE))

/*
 * This mapping is used for the exception handler stack when a synchronous
 * exception is taken.
 */
#define RMM_EH_STACK_MMAP_IDX	0U
#define RMM_EH_STACK_MMAP	MAP_REGION_FULL_SPEC(				\
					0UL, /* PA is different for each CPU */	\
					CPU_EH_STACK_VIRT,			\
					RMM_CPU_EH_STACK_SIZE,			\
					XLAT_NG_DATA_ATTR,			\
					PAGE_SIZE)

#define RMM_STACK_MMAP_IDX	1U
#define RMM_STACK_MMAP		MAP_REGION_FULL_SPEC(				\
					0UL, /* PA is different for each CPU */	\
					CPU_STACK_VIRT,				\
					RMM_CPU_STACK_SIZE,			\
					XLAT_NG_DATA_ATTR,			\
					PAGE_SIZE)

/* The Slot buffers are mapped/unmapped dynamically. Hence define TRANSIENT mmap region */
#define RMM_SLOT_BUF_MMAP	MAP_REGION_TRANSIENT(		\
					SLOT_VIRT,		\
					RMM_SLOT_BUF_SIZE,	\
					PAGE_SIZE)

#define MMAP_REGION_COUNT	3U

/*
 * A single L3 page is used to map the slot buffers as well as the stack, so
 * enforce here that they fit within that L3 page.
 */
COMPILER_ASSERT((RMM_NUM_PAGES_PER_STACK + GAP_PAGE_COUNT + XLAT_HIGH_VA_SLOT_NUM) <=
	XLAT_TABLE_ENTRIES);

/* Context definition */
static struct xlat_ctx high_va_xlat_ctx[MAX_CPUS];

struct xlat_ctx *xlat_get_high_va_xlat_ctx(void)
{
	return &high_va_xlat_ctx[my_cpuid()];
}

/*
 * Setup xlat table for the high VA region for each PE.
 * Must be called for every PE in the system.
 * The layout of the High VA space:
 *
 * +-------------------+  0xFFFFFFFFFFFFFFFF (VA max)
 * |                   |
 * |    Slot buffer    |  XLAT_HIGH_VA_SLOT_NUM * GRANULE_SIZE bytes
 * |                   |
 * +-------------------+
 * |                   |
 * |    Stack guard    |  CPU_STACK_GAP bytes, Unmapped
 * |                   |
 * +-------------------+
 * |                   |
 * |     RMM stack     |  RMM_CPU_STACK_SIZE bytes,
 * |                   |
 * +-------------------+
 * |                   |
 * |    Stack guard    |  CPU_STACK_GAP bytes, Unmapped
 * |                   |
 * +-------------------+
 * |                   |
 * |   RMM exception   |
 * |   handler stack   |  RMM_CPU_EH_STACK_SIZE bytes,
 * |                   |
 * +-------------------+
 * |                   |
 * |      Unmapped     |
 * |                   |
 * +-------------------+  0xFFFFFFFFFFE00000
 */
int xlat_high_va_setup(void)
{
	/* Allocate xlat_ctx_cfg for high VA which will be specific to PEs */
	static struct xlat_ctx_cfg high_va_xlat_ctx_cfgs[MAX_CPUS];
	/* Allocate per-cpu xlat_ctx_tbls */
	static struct xlat_ctx_tbls high_va_tbls[MAX_CPUS];
	/* Allocate xlat_mmap_region for high VA mappings which will be specific to PEs */
	static struct xlat_mmap_region mm_regions_array[MAX_CPUS][MMAP_REGION_COUNT] = {
		[0 ... MAX_CPUS-1] = {RMM_EH_STACK_MMAP, RMM_STACK_MMAP, RMM_SLOT_BUF_MMAP}};
	/*
	 * The base tables for all the contexts are manually allocated as a continuous
	 * block of memory (one L3 table per PE).
	 */
	static uint64_t high_va_tts[XLAT_TABLE_ENTRIES * MAX_CPUS] __aligned(XLAT_TABLES_ALIGNMENT);

	unsigned int cpuid = my_cpuid();
	struct xlat_mmu_cfg mmu_config;
	int ret;

	/* Set handler stack PA for this CPU */
	mm_regions_array[cpuid][RMM_EH_STACK_MMAP_IDX].base_pa =
		rmm_get_my_eh_stack(cpuid) - RMM_CPU_EH_STACK_SIZE;

	/* Set stack PA for this CPU */
	mm_regions_array[cpuid][RMM_STACK_MMAP_IDX].base_pa =
		rmm_get_my_stack(cpuid) - RMM_CPU_STACK_SIZE;

	/* Initialize the context configuration for this CPU */
	ret = xlat_ctx_cfg_init(&high_va_xlat_ctx_cfgs[cpuid], VA_HIGH_REGION,
				 &mm_regions_array[cpuid][0U],
				 MMAP_REGION_COUNT,
				 XLAT_HIGH_VA_SIZE);
	if (!((ret == 0) || (ret == -EALREADY))) {
		return ret;
	}

	/*
	 * Initialize the translation tables for the current context.
	 * This is done on the first boot of each PE.
	 */
	ret = xlat_ctx_init(&high_va_xlat_ctx[cpuid],
				&high_va_xlat_ctx_cfgs[cpuid],
				&high_va_tbls[cpuid],
				&high_va_tts[(size_t)XLAT_TABLE_ENTRIES * cpuid], 1U);

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

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <errno.h>
#include <pcpu_data.h>
/* coverity[unnecessary_header:SUPPRESS] */
#include <string.h>
#include <utils_def.h>
#include <xlat_contexts.h>
#include <xlat_tables.h>

/*
 * The layout of each per-CPU region in physical memory
 * (region base PA == metadata page PA)
 *
 * +----------------------+
 * |                      |
 * |   High VA tables     |  HIGH_VA_TBLS_PAGES
 * |                      |
 * +----------------------+
 * |                      |
 * |   RMM exception      |
 * |   handler stack      |  EH_STACK_PAGES
 * |                      |
 * +----------------------+
 * |                      |
 * |    RMM stack         |  RMM_NUM_PAGES_PER_STACK
 * |                      |
 * +----------------------+
 * |                      |
 * | struct pcpu_metadata | PCPU_METADATA_PAGES
 * |                      |
 * +----------------------+
 */
/*
 * pcpu_metadata_early_init() - Initialize the metadata page that acts as the
 * header for the current CPU's per-CPU region.
 *
 * Also ensure TPIDR_EL2 is set to [per-CPU metadata base | CPU index].
 * The CPU index is encoded in the low GRANULE_SHIFT bits of the per-CPU
 * metadata base address and TPIDR_EL2 is programmed with the result.
 * The EL2 assembly boot path seeds this before the first C call so my_cpuid()
 * is available immediately; fake-host setup reaches this helper directly, so
 * keep the write here as well.
 *
 * Note that pcpu_switch_to_high_va() will later rebuild the same encoding with
 * the fixed high virtual address once the MMU is enabled.
 *
 * Arguments:
 *	pcpu_metadata_pa: Physical address of the metadata page (bits [63:12])
 *	cpu_index: CPU index to encode in lower 12 bits (must be <= 4095)
 *	token: Activation token for the CPU
 *
 * The token is zero only on the first RMM entry on this CPU. On later
 * entries, including warm re-entry through LFA, it carries the base PA of
 * the previously allocated per-CPU region, which is also the PA of the
 * metadata page.
 */
void pcpu_metadata_early_init(unsigned long pcpu_metadata_pa,
			unsigned long cpu_index, uint64_t token)
{
	unsigned long tpidr_value = pcpu_metadata_pa;
	struct pcpu_metadata *pcpu_metadata_ptr = (struct pcpu_metadata *)pcpu_metadata_pa;

	assert(!is_mmu_enabled()); /* Ensure MMU is not enabled yet */

	/* Ensure CPU index fits in 12 bits */
	assert(cpu_index <= (GRANULE_SIZE - 1UL));

	/* Ensure PA is aligned to 4KB (last 12 bits are 0) */
	assert(ALIGNED(pcpu_metadata_pa, GRANULE_SIZE));

	/* Encode CPU index in the last 12 bits of the metadata PA */
	tpidr_value |= cpu_index;
	write_tpidr_el2(tpidr_value);

	if (token != 0UL) {
		/* Ensure PA from argument matches token */
		assert(pcpu_metadata_pa == token);
		/* Metadata is already initialized, no need to reinitialize */
		return;
	}

	/* Set version */
	pcpu_metadata_ptr->version = 1;
	/* Initialize global data PA to 0, will be set later */
	pcpu_metadata_ptr->glob_data_pa = 0UL;

	/*
	 * Record the physical layout of this CPU's region. The metadata page is
	 * the first granule, so the metadata base PA is also the region base PA.
	 */
	pcpu_metadata_ptr->metadata_base_pa = pcpu_metadata_pa;
	pcpu_metadata_ptr->metadata_top_pa = pcpu_metadata_ptr->metadata_base_pa +
					(PCPU_METADATA_PAGES * GRANULE_SIZE);

	pcpu_metadata_ptr->stack_base_pa = pcpu_metadata_ptr->metadata_top_pa;
	pcpu_metadata_ptr->stack_top_pa = pcpu_metadata_ptr->stack_base_pa +
					(RMM_NUM_PAGES_PER_STACK * GRANULE_SIZE);

	pcpu_metadata_ptr->eh_stack_base_pa = pcpu_metadata_ptr->stack_top_pa;
	pcpu_metadata_ptr->eh_stack_top_pa = pcpu_metadata_ptr->eh_stack_base_pa +
					(EH_STACK_PAGES * GRANULE_SIZE);

	pcpu_metadata_ptr->high_va_tbls_base_pa = pcpu_metadata_ptr->eh_stack_top_pa;
	pcpu_metadata_ptr->high_va_tbls_top_pa =
				pcpu_metadata_ptr->high_va_tbls_base_pa +
				(HIGH_VA_TBLS_PAGES * GRANULE_SIZE);

	(void)memset(&pcpu_metadata_ptr->high_va_xlat_ctx, 0, sizeof(struct xlat_ctx));
	assert((pcpu_metadata_ptr->high_va_tbls_top_pa) ==
		(pcpu_metadata_pa + (PCPU_REGION_PAGES * GRANULE_SIZE)));

	/* No need to invalidate the entire struct, only the size of the initialized fields */
	inv_dcache_range(pcpu_metadata_pa,
		offsetof(struct pcpu_metadata, eh_stack_top_pa) + sizeof(uintptr_t));
}

uintptr_t pcpu_get_region_base_pa(void)
{
	return my_pcpu_metadata()->metadata_base_pa;
}

uintptr_t pcpu_get_glob_data_pa(void)
{
	return my_pcpu_metadata()->glob_data_pa;
}

void pcpu_set_glob_data_pa(uintptr_t glob_data_pa)
{
	struct pcpu_metadata *metadata = my_pcpu_metadata();
	assert(is_mmu_enabled());

	/* If the global data PA is already set, ensure it matches */
	if (metadata->glob_data_pa != 0UL) {
		assert(metadata->glob_data_pa == glob_data_pa);
		return; /* No change needed */
	}

	metadata->glob_data_pa = glob_data_pa;
	/* Ensure the updated global data PA is visible even if read with MMU off */
	flush_dcache_range((uintptr_t)&metadata->glob_data_pa,
			   sizeof(metadata->glob_data_pa));
}

/* Size of Slot Buffer in bytes. */
#define RMM_SLOT_BUF_SIZE	((XLAT_HIGH_VA_SLOT_NUM) * (GRANULE_SIZE))

/* This mapping is used for the metadata page (`struct pcpu_metadata`). */
#define RMM_PCPU_METADATA_MMAP_IDX	0U
#define RMM_PCPU_METADATA_MMAP	MAP_REGION_FULL_SPEC(					\
					0UL, /* PA is different for each CPU */		\
					PCPU_METADATA_BASE_VA,			\
					(PCPU_METADATA_PAGES * GRANULE_SIZE),	\
					XLAT_NG_DATA_ATTR,				\
					GRANULE_SIZE)

/* This mapping is used for the RMM stack */
#define RMM_STACK_MMAP_IDX	1U
#define RMM_STACK_MMAP		MAP_REGION_FULL_SPEC(					\
					0UL, /* PA is different for each CPU */		\
					STACK_BASE_VA,				\
					(RMM_NUM_PAGES_PER_STACK * GRANULE_SIZE),	\
					XLAT_NG_DATA_ATTR,				\
					GRANULE_SIZE)

/* This mapping is used for the exception handler stack */
#define RMM_EH_STACK_MMAP_IDX	2U
#define RMM_EH_STACK_MMAP	MAP_REGION_FULL_SPEC(					\
					0UL, /* PA is different for each CPU */		\
					EH_STACK_BASE_VA,				\
					(EH_STACK_PAGES * GRANULE_SIZE), 	\
					XLAT_NG_DATA_ATTR,				\
					GRANULE_SIZE)

/* This mapping is used for the per-CPU high-VA page tables. */
#define RMM_HIGH_VA_TBLS_MMAP_IDX	3U
#define RMM_HIGH_VA_TBLS_MMAP	MAP_REGION_FULL_SPEC(					\
					0UL, /* PA is different for each CPU */			\
					HIGH_VA_TBLS_BASE_VA,					\
					(HIGH_VA_TBLS_PAGES * GRANULE_SIZE),		\
					XLAT_NG_DATA_ATTR,					\
					GRANULE_SIZE)

/*
 * The Slot buffers are mapped/unmapped dynamically (they have a fixed, reserved VA range,
 * but they don't have fixed physical pages associated).
 * Hence define TRANSIENT mmap region.
 */
#define RMM_SLOT_BUF_MMAP_IDX	4U
#define RMM_SLOT_BUF_MMAP	MAP_REGION_TRANSIENT(		\
					SLOT_BUFFER_BASE_VA,	\
					RMM_SLOT_BUF_SIZE,	\
					GRANULE_SIZE)

#define MMAP_REGION_COUNT	5U

/*
 * A single L3 page is used to map the full per-CPU high-VA layout, including
 * the metadata page, stacks, page tables, and slot buffers, so enforce here
 * that they fit within that L3 page.
 */
COMPILER_ASSERT_NO_CBMC((PCPU_REGION_TOTAL_VA_PAGES + XLAT_HIGH_VA_SLOT_NUM) <=
					XLAT_TABLE_ENTRIES);

/*
 * The layout of the High VA space:
 * The same virtual addresses are reused on every CPU, but each CPU maps them
 * to its own per-CPU physical region.
 *
 * +----------------------+  0xFFFFFFFFFFFFFFFF (VA max)
 * |                      |
 * |    Slot buffer       |  XLAT_HIGH_VA_SLOT_NUM * GRANULE_SIZE bytes
 * |                      |
 * +----------------------+
 * |                      |
 * | High VA PT guard     |  PCPU_GUARD_GAP_PAGES Unmapped
 * |                      |
 * +----------------------+
 * |                      |
 * |   High VA tables     |  HIGH_VA_TBLS_PAGES Mapped
 * |                      |
 * +----------------------+
 * |                      |
 * |   EH stack guard     |  PCPU_GUARD_GAP_PAGES Unmapped
 * |                      |
 * +----------------------+
 * |                      |
 * |   RMM exception      |
 * |   handler stack      |  EH_STACK_PAGES Mapped
 * |                      |
 * +----------------------+
 * |                      |
 * |    Stack guard       |  PCPU_GUARD_GAP_PAGES Unmapped
 * |                      |
 * +----------------------+
 * |                      |
 * |    RMM stack         |  RMM_NUM_PAGES_PER_STACK Mapped
 * |                      |
 * +----------------------+
 * |                      |
 * | Per-CPU metadata     |  PCPU_GUARD_GAP_PAGES Unmapped
 * |       guard          |
 * |                      |
 * +----------------------+
 * |                      |
 * | struct pcpu_metadata | PCPU_METADATA_PAGES Mapped
 * |                      |
 * +----------------------+
 * |                      |
 * |      Unmapped        |
 * |                      |
 * +----------------------+  0xFFFFFFFFFFE00000
 */
int pcpu_high_va_setup(void)
{
	struct xlat_mmu_cfg mmu_config;
	int ret;

	/* Allocate xlat_mmap_region for high VA mappings which will be specific to PEs */
	struct xlat_mmap_region mm_regions_array[MMAP_REGION_COUNT] = {
		[RMM_PCPU_METADATA_MMAP_IDX] = RMM_PCPU_METADATA_MMAP,
		[RMM_STACK_MMAP_IDX]	= RMM_STACK_MMAP,
		[RMM_EH_STACK_MMAP_IDX]	= RMM_EH_STACK_MMAP,
		[RMM_HIGH_VA_TBLS_MMAP_IDX] = RMM_HIGH_VA_TBLS_MMAP,
		[RMM_SLOT_BUF_MMAP_IDX]	= RMM_SLOT_BUF_MMAP
	};

	assert(is_mmu_enabled() == false);
	struct pcpu_metadata *pcpu_metadata_ptr = my_pcpu_metadata();

	/* Since MMU is not enabled metadata_base_pa should match the address of the struct */
	assert(pcpu_metadata_ptr->metadata_base_pa == (uintptr_t)pcpu_metadata_ptr);

	/*
	 * Install the current CPU's physical per-CPU region into the fixed high-VA
	 * layout. Every CPU uses the same metadata/stack/page-table VAs, but those
	 * VAs resolve to the current CPU's own metadata page, stacks, and page
	 * tables.
	 */
	mm_regions_array[RMM_PCPU_METADATA_MMAP_IDX].base_pa =
		pcpu_metadata_ptr->metadata_base_pa;
	mm_regions_array[RMM_STACK_MMAP_IDX].base_pa =
		pcpu_metadata_ptr->stack_base_pa;
	mm_regions_array[RMM_EH_STACK_MMAP_IDX].base_pa =
		pcpu_metadata_ptr->eh_stack_base_pa;
	mm_regions_array[RMM_HIGH_VA_TBLS_MMAP_IDX].base_pa =
		pcpu_metadata_ptr->high_va_tbls_base_pa;

	/* Initialize the context configuration for this CPU */
	ret = xlat_ctx_cfg_init(&pcpu_metadata_ptr->high_va_xlat_ctx, VA_HIGH_REGION,
				 mm_regions_array, MMAP_REGION_COUNT,
				 0UL, XLAT_HIGH_VA_SIZE, RMM_ASID);
	if ((ret != 0) && (ret != -EALREADY)) {
		return ret;
	}

	/*
	 * Initialize the translation tables for the current context.
	 * This is done on the first boot of each PE.
	 */
	ret = xlat_ctx_init_remapped_tbls(&pcpu_metadata_ptr->high_va_xlat_ctx,
				(uint64_t *)pcpu_metadata_ptr->high_va_tbls_base_pa,
				HIGH_VA_TBLS_PAGES,
				pcpu_metadata_ptr->high_va_tbls_base_pa,
				HIGH_VA_TBLS_BASE_VA);

	if ((ret != 0) && (ret != -EALREADY)) {
		return ret;
	}

	/* Configure MMU registers */
	ret = xlat_arch_setup_mmu_cfg(&pcpu_metadata_ptr->high_va_xlat_ctx, &mmu_config);

	if (ret == 0) {
		xlat_arch_write_mmu_cfg(&mmu_config);
	}

	return ret;
}

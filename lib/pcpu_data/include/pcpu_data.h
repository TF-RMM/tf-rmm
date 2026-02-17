/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PCPU_DATA_H
#define PCPU_DATA_H

#if !(defined(__ASSEMBLER__) || defined(__LINKER__))
#include <arch_helpers.h>
#include <stdint.h>
#endif
#include <utils_def.h>
#include <xlat_contexts.h>
#include <xlat_tables.h>

/******************************************************************************
 * Per-CPU Region Physical Page Layout
 *
 * This module manages one per-CPU memory region for each CPU. The first
 * physical granule of that region stores `struct pcpu_metadata`. The remaining
 * granules store the regular RMM stack, the exception-handler stack, and the
 * per-CPU high-VA page tables.
 *
 * Because the metadata page is the first granule of the region, the base
 * physical address of the per-CPU region is also the physical address of the
 * metadata page. The activation token passed back to EL3 is equal to that base
 * physical address so a later entry on the same CPU can recover the region.
 *
 * The physical layout is described in `pcpu_data.c`.
 ******************************************************************************/

/* Number of physical pages used by the metadata page (`struct pcpu_metadata`). */
#define PCPU_METADATA_PAGES	U(1)
/* Base physical address of the regular RMM stack. */
#define PCPU_STACK_BASE_PA_OFFSET	(PCPU_METADATA_PAGES * GRANULE_SIZE)
#define PCPU_STACK_TOP_PA_OFFSET	(PCPU_STACK_BASE_PA_OFFSET + (RMM_NUM_PAGES_PER_STACK * GRANULE_SIZE))
/* Number of physical pages allocated for the exception-handler stack. */
#define EH_STACK_PAGES			U(1)
/* Number of physical pages allocated for the per-CPU high-VA page tables. */
#define HIGH_VA_TBLS_PAGES	U(1)
/* Total number of physical pages in one per-CPU region. */
#define PCPU_REGION_PAGES		(PCPU_METADATA_PAGES + \
						RMM_NUM_PAGES_PER_STACK + \
						EH_STACK_PAGES + \
						HIGH_VA_TBLS_PAGES)

/******************************************************************************
 * Per-CPU High VA Layout
 *
 * Each CPU gets the same fixed high-VA layout for its metadata page, stacks,
 * and slot-buffer window. However, even though the VAs are the same
 * across all CPUs, they are mapped to different physical pages (given by EL3).
 *
 * The VA layout is described in `pcpu_data.c`.
 ******************************************************************************/

/*
 * The number of slot-buffer pages. These pages are part of the high VA region of each CPU.
 * This is an arbitrary constant that must be >= NR_CPU_SLOTS.
 */
#define XLAT_HIGH_VA_SLOT_NUM	(U(115))

/*
 * Translation-table attributes for per-CPU private high-VA mappings.
 * MT_NG marks these entries as non-global, so each CPU can use the same VA
 * range while mapping it to its own private physical pages.
 */
#define XLAT_NG_DATA_ATTR	(MT_RW_DATA | MT_NG)

/*
 * Translation-table attributes for per-CPU private high-VA device mappings.
 * MT_NG marks these entries as non-global for the same reason as above.
 */
#define XLAT_NG_DEV_ATTR	(MT_RW_DEV | MT_NG)

/* Total size of the per-CPU high-VA window described by one translation table. */
#define XLAT_HIGH_VA_SIZE	(XLAT_TABLE_ENTRIES * PAGE_SIZE)

/* Calculate the slot buffer's base virtual address (the top is the maximum possible VA). */
#define SLOT_BUFFER_BASE_VA	(((UL(0xFFFFFFFFFFFFFFFF)) - \
					(XLAT_HIGH_VA_SLOT_NUM * GRANULE_SIZE)) + U(1))

/* Virtual guard pages between each adjacent high-VA mapping. */
#define PCPU_GUARD_GAP_PAGES	U(1)

/*
 * Total number of virtual pages used for the per-CPU region and its guard
 * pages.
 * It includes the stack guards, but not the pages for the Slot Buffer.
 */
#define PCPU_REGION_TOTAL_VA_PAGES	(PCPU_REGION_PAGES + \
					(U(4) * PCPU_GUARD_GAP_PAGES))

/* Virtual address boundaries of the fixed per-CPU high-VA layout. */
#define PCPU_METADATA_BASE_VA	(SLOT_BUFFER_BASE_VA - \
						(PCPU_REGION_TOTAL_VA_PAGES * GRANULE_SIZE))
#define PCPU_METADATA_TOP_VA	(PCPU_METADATA_BASE_VA + \
						(PCPU_METADATA_PAGES * GRANULE_SIZE))
#define STACK_BASE_VA			(PCPU_METADATA_TOP_VA + \
						(PCPU_GUARD_GAP_PAGES * GRANULE_SIZE))
#define STACK_TOP_VA			(STACK_BASE_VA + \
						(RMM_NUM_PAGES_PER_STACK * GRANULE_SIZE))
#define EH_STACK_BASE_VA		(STACK_TOP_VA + \
						(PCPU_GUARD_GAP_PAGES * GRANULE_SIZE))
#define EH_STACK_TOP_VA			(EH_STACK_BASE_VA + \
						(EH_STACK_PAGES * GRANULE_SIZE))
#define HIGH_VA_TBLS_BASE_VA		(EH_STACK_TOP_VA + \
						(PCPU_GUARD_GAP_PAGES * GRANULE_SIZE))
#define HIGH_VA_TBLS_TOP_VA		(HIGH_VA_TBLS_BASE_VA + \
						(HIGH_VA_TBLS_PAGES * GRANULE_SIZE))

#if !(defined(__ASSEMBLER__) || defined(__LINKER__))

/*
 * In-memory header stored in the first granule of each per-CPU region.
 *
 * This struct does not hold the contents of the stacks. Instead it describes
 * the current CPU's per-CPU region and records the physical address ranges of
 * the region itself, the regular RMM stack, the exception-handler stack, and
 * the per-CPU high-VA page tables.
 *
 * TPIDR_EL2 always points at this metadata page for the current CPU, either
 * through its physical address during early boot or through its fixed high VA
 * after pcpu_switch_to_high_va().
 */
struct pcpu_metadata {
	/* Format version of this metadata page. */
	uint64_t version;

	/* Physical address of the shared global-data region. */
	uintptr_t glob_data_pa;

	/*
	 * Physical address of the beginning of the metadata page.
	 * This is also the physical address of this struct.
	 */
	uintptr_t metadata_base_pa;

	/* Equal to metadata_base_pa + PCPU_METADATA_PAGES * GRANULE_SIZE. */
	uintptr_t metadata_top_pa;

	/*
	 * Equal to metadata_base_pa + PCPU_METADATA_PAGES * GRANULE_SIZE.
	 * Also equal to metadata_top_pa.
	 */
	uintptr_t stack_base_pa;

	/* Equal to stack_base_pa + RMM_NUM_PAGES_PER_STACK * GRANULE_SIZE. */
	uintptr_t stack_top_pa;

	/*
	 * Equal to stack_base_pa + RMM_NUM_PAGES_PER_STACK * GRANULE_SIZE.
	 * Also equal to stack_top_pa.
	 */
	uintptr_t eh_stack_base_pa;

	/* Equal to eh_stack_base_pa + EH_STACK_PAGES * GRANULE_SIZE. */
	uintptr_t eh_stack_top_pa;

	/*
	 * Physical address range of the high-VA page tables for this CPU.
	 *
	 * Equal to eh_stack_base_pa + EH_STACK_PAGES * GRANULE_SIZE.
	 * Also equal to eh_stack_top_pa.
	 */
	uintptr_t high_va_tbls_base_pa;

	/*
	 * Equal to
	 * high_va_tbls_base_pa + HIGH_VA_TBLS_PAGES * GRANULE_SIZE.
	 */
	uintptr_t high_va_tbls_top_pa;

	/* High-VA translation context stored in the metadata page for this CPU. */
	struct xlat_ctx high_va_xlat_ctx;

} __aligned(GRANULE_SIZE);

COMPILER_ASSERT(sizeof(struct pcpu_metadata) == GRANULE_SIZE);
COMPILER_ASSERT(MAX_CPUS <= GRANULE_SIZE);


/*
 * TPIDR_EL2 always stores the base address of the current CPU's metadata
 * granule, with the CPU index encoded in the low GRANULE_SHIFT bits.
 *
 * Before pcpu_switch_to_high_va(), that base address is a physical address.
 * Afterwards, it is the fixed high virtual address PCPU_METADATA_BASE_VA.
 *
 * Since the metadata page is the first granule of the per-CPU region, masking
 * out the CPU ID also gives the base address of the current CPU's region.
 */
static inline struct pcpu_metadata *my_pcpu_metadata(void)
{
	return (struct pcpu_metadata *)(read_tpidr_el2() & GRANULE_MASK);
}

/* Return a pointer to the High VA xlat context for the current CPU */
static inline struct xlat_ctx *pcpu_high_va_xlat_ctx(void)
{
	return &my_pcpu_metadata()->high_va_xlat_ctx;
}

void pcpu_metadata_early_init(unsigned long pcpu_metadata_pa,
			unsigned long cpu_index, uint64_t token);
uintptr_t pcpu_get_region_base_pa(void);
uintptr_t pcpu_get_glob_data_pa(void);
void pcpu_set_glob_data_pa(uintptr_t glob_data_pa);
int pcpu_high_va_setup(void);
uintptr_t pcpu_region_alloc(uint64_t token);
void pcpu_switch_to_high_va(void);
void pcpu_fake_host_setup(unsigned long cpu_index, uint64_t token);

/* Functions to read/write from/to specific fields in struct here */
#endif /* !(defined(__ASSEMBLER__) || defined(__LINKER__)) */
#endif /* PCPU_DATA_H */

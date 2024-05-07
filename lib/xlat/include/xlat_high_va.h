/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef XLAT_HIGH_VA_H
#define XLAT_HIGH_VA_H

#include <utils_def.h>
#include <xlat_tables.h>

/* The per CPU High VA space is used for Slot buffer and per-CPU stack mapping */
#define XLAT_HIGH_VA_SLOT_NUM	(U(108))

/* Calculate the slot buffer's virtual address */
#define SLOT_VIRT		(((UL(0xFFFFFFFFFFFFFFFF)) - \
				(XLAT_HIGH_VA_SLOT_NUM * GRANULE_SIZE)) + 1U)

#define RMM_CPU_STACK_SIZE		(RMM_NUM_PAGES_PER_STACK * PAGE_SIZE)
#define RMM_CPU_EH_STACK_SIZE		PAGE_SIZE

/* Leave some pages of gap above the stack top */
#define GAP_PAGE_COUNT			(U(1))
#define CPU_STACK_GAP			(GAP_PAGE_COUNT * PAGE_SIZE)
#define RMM_CPU_STACK_END_VA		(SLOT_VIRT - CPU_STACK_GAP)
#define CPU_STACK_VIRT			(RMM_CPU_STACK_END_VA - RMM_CPU_STACK_SIZE)

/* Exception stack defines */
#define RMM_CPU_EH_STACK_END_VA		(CPU_STACK_VIRT - CPU_STACK_GAP)
#define CPU_EH_STACK_VIRT		(RMM_CPU_EH_STACK_END_VA - RMM_CPU_EH_STACK_SIZE)

/* TTE attribute for per CPU private VA (nG) Data mapping) */
#define XLAT_NG_DATA_ATTR	(MT_RW_DATA | MT_NG)

#define XLAT_HIGH_VA_SIZE	(XLAT_TABLE_ENTRIES * PAGE_SIZE)

#if !(defined(__ASSEMBLER__) || defined(__LINKER__))

/* Return a pointer to the High VA xlat context for the current CPU */
struct xlat_ctx *xlat_get_high_va_xlat_ctx(void);

/*
 * Initializes and enables the VMSA for the high va region.
 *
 * Create an empty translation context for the current PE.
 * If the context already exists (e.g. current PE was previously
 * turned on and therefore the context is already in memory),
 * nothing happens.
 */
int xlat_high_va_setup(void);

/* Return the physical address of the stack used by the exception handler for a given PE index */
/* The function is defined in assembly, so suppressing misra error: */
/* coverity[misra_c_2012_rule_8_6_violation:SUPPRESS] */
uintptr_t rmm_get_my_eh_stack(unsigned long cpuid);

/* Return the stack physical address for a given PE index */
/* The function is defined in assembly, so suppressing misra error: */
/* coverity[misra_c_2012_rule_8_6_violation:SUPPRESS] */
uintptr_t rmm_get_my_stack(unsigned long cpuid);

#endif /* !(defined(__ASSEMBLER__) || defined(__LINKER__)) */

#endif /* XLAT_HIGH_VA_H */

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef APP_FW_STRUCTURES_H
#define APP_FW_STRUCTURES_H

#include <utils_def.h>
#include <xlat_high_va.h>

#define APP_SAVED_GEN_REG_COUNT		U(31)

#define APP_XLAT_TABLE_COUNT		U(1)

#define APP_TTBR1_EL2_OFFSET		UL(0)
#define RMM_TTBR1_EL2_OFFSET		UL(8)
#define RMM_VBAR_EL2_OFFSET		UL(16)
#define RMM_TPIDR_EL0_OFFSET		UL(24)
#define RMM_TPIDRRO_EL0_OFFSET		UL(32)
#define PC_OFFSET			UL(40)
#define PSTATE_OFFSET			UL(48)
#define APP_SAVED_REGS_OFFSET		UL(56)
#define SP_EL0_OFFSET			UL(304)

#ifndef __ASSEMBLER__

/* This structure must always be aligned to page boundary as it is mapped into
 * the app VA space.
 */
struct app_reg_ctx {
	/*
	 * Members are defined with macros to make sure that the member offsets
	 * that are used by the assembly code are aligned with the structure
	 * definition.
	 */
	SET_MEMBER(uint64_t app_ttbr1_el2, APP_TTBR1_EL2_OFFSET, RMM_TTBR1_EL2_OFFSET);
	SET_MEMBER(uint64_t rmm_ttbr1_el2, RMM_TTBR1_EL2_OFFSET, RMM_VBAR_EL2_OFFSET);
	SET_MEMBER(uint64_t rmm_vbar_el2, RMM_VBAR_EL2_OFFSET, RMM_TPIDR_EL0_OFFSET);
	SET_MEMBER(uint64_t rmm_tpidr_el0, RMM_TPIDR_EL0_OFFSET, RMM_TPIDRRO_EL0_OFFSET);
	SET_MEMBER(uint64_t rmm_tpidrro_el0, RMM_TPIDRRO_EL0_OFFSET, PC_OFFSET);
	SET_MEMBER(uint64_t pc, PC_OFFSET, PSTATE_OFFSET);
	SET_MEMBER(uint64_t pstate, PSTATE_OFFSET, APP_SAVED_REGS_OFFSET);
	SET_MEMBER(uint64_t app_regs[APP_SAVED_GEN_REG_COUNT],
		APP_SAVED_REGS_OFFSET, SP_EL0_OFFSET);
	SET_MEMBER(uint64_t sp_el0, SP_EL0_OFFSET, GRANULE_SIZE);
} __aligned(GRANULE_SIZE);
COMPILER_ASSERT(sizeof(struct app_reg_ctx) == GRANULE_SIZE);
COMPILER_ASSERT(SIZEOF_MEMBER(struct app_reg_ctx, app_regs) ==
			(sizeof(unsigned long) * APP_SAVED_GEN_REG_COUNT));
/*
 * NS_TPIDR[RO]_EL0_OFFSET registers are saved/restored with a single stp/ldr
 * instruction, so they must be close.
 */
COMPILER_ASSERT((RMM_TPIDR_EL0_OFFSET + sizeof(unsigned long)) == RMM_TPIDRRO_EL0_OFFSET);
/*
 * The code entering and exiting from EL0 app assumes that sp_el0 is
 * right after the `regs` array.
 */
COMPILER_ASSERT(U(offsetof(struct app_reg_ctx, sp_el0)) ==
	(U(offsetof(struct app_reg_ctx, app_regs)) +
		(APP_SAVED_GEN_REG_COUNT * sizeof(unsigned long))));
/* Make sure that the last member in the list is at the desired offset */
COMPILER_ASSERT(U(offsetof(struct app_reg_ctx, sp_el0)) == SP_EL0_OFFSET);

struct app_data_cfg {
	/* Structures for setting up and storing app translation related data */
	struct xlat_ctx app_va_xlat_ctx;
	struct xlat_mmu_cfg mmu_config;
	struct xlat_llt_info cached_app_llt_info;
	uintptr_t app_reg_ctx_pa;

	uintptr_t shared_page_pa;
	uintptr_t el0_shared_page_va;
	void *el2_shared_page; /* Is NULL while the shared page is not mapped */
	void *el2_heap_start; /* The start VA in the EL2 VA space of the app heap area */
	uintptr_t heap_va; /* this VA address is valid in the EL0 VA space */
	uintptr_t heap_size;
	uintptr_t stack_buf_start_va;
	uintptr_t stack_top; /* Initial value of the stack pointer */

	/* App entry point VA */
	uintptr_t entry_point;

	bool app_entered;
	uint32_t exit_flag; /* App Exit Flag */
};
COMPILER_ASSERT((XLAT_TABLE_ENTRIES * APP_XLAT_TABLE_COUNT) <= GRANULE_SIZE);

#endif /* __ASSEMBLER__ */
#endif /* APP_FW_STRUCTURES_H */

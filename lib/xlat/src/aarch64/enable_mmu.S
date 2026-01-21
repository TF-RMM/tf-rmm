/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

/* This file is derived from xlat_table_v2 library in TF-A project */

#include <asm_macros.S>
#include <xlat_high_va.h>
#include <xlat_tables.h>

	.global	xlat_enable_mmu_el2

	func xlat_enable_mmu_el2
		dsb	ish

		/* Invalidate all TLB entries */
		TLB_INVALIDATE(alle2)

		/*
		 * Ensure all translation table writes have drained into memory, the TLB
		 * invalidation is complete, and translation register writes are
		 * committed before enabling the MMU
		 */
		dsb	ish
		isb

		/* Set and clear required fields of SCTLR */
		mrs	x4, sctlr_el2
		mov_imm	x5, SCTLR_ELx_WXN_BIT | SCTLR_ELx_M_BIT
		orr	x4, x4, x5
		msr	sctlr_el2, x4

		/*
		 * Update SP to point to the VA of the stack bottom for this
		 * CPU after enabling MMU
		 */
		mov_imm	x5, RMM_CPU_STACK_END_VA
		mov	sp, x5
		/* Also set the exception handler stack */
		mov_imm	x5, RMM_CPU_EH_STACK_END_VA
		msr	sp_el0, x5

		isb

		ret
	endfunc xlat_enable_mmu_el2

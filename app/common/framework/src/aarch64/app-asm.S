/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <arch.h>
#include <asm_macros.S>
#include <xlat_high_va.h>

.globl run_app
.globl app_exit

	.section ".text"

/* TODO: It should be possible to encode the lower EL state in tpidr_el2 and the
 * vectors could check this to differentiate between running VHE EL0 mode or
 * Realms. This could make it possible to unify the two vector tables.
 */
ENTRY(app_vectors):
	ventry_unused	exc_sync_sp0
	ventry_unused	exc_irq_sp0
	ventry_unused	exc_fiq_sp0
	ventry_unused	exc_serror_sp0

	ventry_unused	exc_sync_spx
	ventry_unused	exc_irq_spx
	ventry_unused	exc_fiq_spx
	ventry_unused	exc_serror_spx

	ventry		el2_sync_lel
	ventry_unused	el2_irq_lel
	ventry_unused	el2_fiq_lel
	ventry_unused	el2_serror_lel

	ventry_unused	exc_sync_lel_32
	ventry_unused	exc_irq_lel_32
	ventry_unused	exc_fiq_lel_32
	ventry_unused	exc_serror_lel_32
ENDPROC(app_vectors)

el2_sync_lel:
	msr	tpidr_el0, x0
	mov	x0, #ARM_EXCEPTION_SYNC_LEL
	b	back_from_el0
ENDPROC(el2_sync_lel)

/*
 * int run_app(struct app_reg_ctx* app_reg_ctx, uint64_t heap_properties);
 *
 * Per the AAPCS the function must preserve x19-x29, along with the SP. The
 * function may freely corrupt x0-18 and the flags, but needs the LR to return
 * to its caller.
 */
func run_app
	/* Push RMM registers to the stack */
	sub	sp, sp, #(16 * 6)
	stp	x19, x20, [sp, #(16 * 0)]
	stp	x21, x22, [sp, #(16 * 1)]
	stp	x23, x24, [sp, #(16 * 2)]
	stp	x25, x26, [sp, #(16 * 3)]
	stp	x27, x28, [sp, #(16 * 4)]
	stp	x29, x30, [sp, #(16 * 5)]

	/* save TPIDR* registers */
	mrs	x19, tpidr_el0
	mrs	x20, tpidrro_el0
	stp	x19, x20, [x0, #RMM_TPIDR_EL0_OFFSET]

	/* Set heap properties in TPIDRRO_EL0 for the app to read */
	msr	tpidrro_el0, x1

	/* save RMM TTBR */
	mrs	x1, ttbr1_el2
	str	x1, [x0, #RMM_TTBR1_EL2_OFFSET]

	/* Save original vbar_el2 */
	mrs	x1, vbar_el2
	str	x1, [x0, #RMM_VBAR_EL2_OFFSET]

	/* Update TTBR register:
	 * Point ttbr1_el2 to the app's translation table
	 */
	ldr	x1, [x0, #APP_TTBR1_EL2_OFFSET]
	msr	ttbr1_el2, x1

	/* Invalidate TLB for the App ASID. The ASID is extracted from the TTBR
	 * value. The ASID is encoded in the bits [63:48] in both the TTBR value
	 * and in the TLBI operand, so here only bits [47:0] needs to be
	 * cleared.
	 */
	/* TODO: Further optimise TLB management.
	 * - Since Text, RO, RW and BSS are shared for all the instances of the
	 *   App, here we could do a TLBI ASID only for the instance specific
	 *   memory like stack, heap and shared memory.
	 * - There is a further optimization for App instances specific to CPU.
	 *   By using special ASID for CPU app instances (for example MSB set),
	 *   TLB invalidation for those can be omitted.
	 */
	and	x1, x1, #(~((1 << 48) - 1))
	tlbi	aside1, x1
	dsb	nsh
	isb

	/* starting from this point the app mapping is active, so to access
	 * app_reg_ctx, it must be done via the VA in the app mapping.
	 * So update x0.
	 */
	mov_imm	x0, APP_VA_START

	/* Disable Low VA range for unprivileged code */
	mrs	x1, tcr_el2
	orr	x1, x1, #TCR_EL2_E0PD0
	msr	tcr_el2, x1

	/* update the vector table base address to the app_return vector */
	adrp	x1, app_vectors
	add	x1, x1, :lo12:app_vectors
	msr	vbar_el2, x1
	isb

	/* load app GPRs */
	ldp	x2,  x3,  [x0, #(APP_SAVED_REGS_OFFSET + 16 * 1)]
	ldp	x4,  x5,  [x0, #(APP_SAVED_REGS_OFFSET + 16 * 2)]
	ldp	x6,  x7,  [x0, #(APP_SAVED_REGS_OFFSET + 16 * 3)]
	ldp	x8,  x9,  [x0, #(APP_SAVED_REGS_OFFSET + 16 * 4)]
	ldp	x10, x11, [x0, #(APP_SAVED_REGS_OFFSET + 16 * 5)]
	ldp	x12, x13, [x0, #(APP_SAVED_REGS_OFFSET + 16 * 6)]
	ldp	x14, x15, [x0, #(APP_SAVED_REGS_OFFSET + 16 * 7)]
	ldp	x16, x17, [x0, #(APP_SAVED_REGS_OFFSET + 16 * 8)]
	ldp	x18, x19, [x0, #(APP_SAVED_REGS_OFFSET + 16 * 9)]
	ldp	x20, x21, [x0, #(APP_SAVED_REGS_OFFSET + 16 * 10)]
	ldp	x22, x23, [x0, #(APP_SAVED_REGS_OFFSET + 16 * 11)]
	ldp	x24, x25, [x0, #(APP_SAVED_REGS_OFFSET + 16 * 12)]
	ldp	x26, x27, [x0, #(APP_SAVED_REGS_OFFSET + 16 * 13)]
	ldp	x28, x29, [x0, #(APP_SAVED_REGS_OFFSET + 16 * 14)]
	ldr	x30,      [x0, #(APP_SAVED_REGS_OFFSET + 16 * 15)]
	ldr	x1,       [x0, #(APP_SAVED_REGS_OFFSET + 16 * 15 + 8)]
	msr	sp_el0, x1
	ldp	x0,  x1,  [x0, #(APP_SAVED_REGS_OFFSET + 16 * 0)]

	eret
	sb

endfunc run_app

func back_from_el0

	/* Load the address of the app_reg_ctx to x1 */
	msr	tpidrro_el0, x1
	mov_imm	x1, APP_VA_START

	/* Store app GPRs */
	stp	x2,  x3,  [x1, #(APP_SAVED_REGS_OFFSET + 16 * 1)]
	stp	x4,  x5,  [x1, #(APP_SAVED_REGS_OFFSET + 16 * 2)]
	stp	x6,  x7,  [x1, #(APP_SAVED_REGS_OFFSET + 16 * 3)]
	stp	x8,  x9,  [x1, #(APP_SAVED_REGS_OFFSET + 16 * 4)]
	stp	x10, x11, [x1, #(APP_SAVED_REGS_OFFSET + 16 * 5)]
	stp	x12, x13, [x1, #(APP_SAVED_REGS_OFFSET + 16 * 6)]
	stp	x14, x15, [x1, #(APP_SAVED_REGS_OFFSET + 16 * 7)]
	stp	x16, x17, [x1, #(APP_SAVED_REGS_OFFSET + 16 * 8)]
	stp	x18, x19, [x1, #(APP_SAVED_REGS_OFFSET + 16 * 9)]
	stp	x20, x21, [x1, #(APP_SAVED_REGS_OFFSET + 16 * 10)]
	stp	x22, x23, [x1, #(APP_SAVED_REGS_OFFSET + 16 * 11)]
	stp	x24, x25, [x1, #(APP_SAVED_REGS_OFFSET + 16 * 12)]
	stp	x26, x27, [x1, #(APP_SAVED_REGS_OFFSET + 16 * 13)]
	stp	x28, x29, [x1, #(APP_SAVED_REGS_OFFSET + 16 * 14)]
	str	x30,      [x1, #(APP_SAVED_REGS_OFFSET + 16 * 15)]
	mrs	x2, sp_el0
	str	x2,       [x1, #(APP_SAVED_REGS_OFFSET + 16 * 15 + 8)]

	/* Load the exception handler stack bottom to SP_EL0 */
	mov_imm	x2, RMM_CPU_EH_STACK_END_VA
	msr	sp_el0, x2

	/* x0 and x1 as stored by el2_vectors and this function */
	mrs	x2, tpidr_el0
	mrs	x3, tpidrro_el0
	stp	x2, x3,   [x1, #(APP_SAVED_REGS_OFFSET + 16 * 0)]

	/* restore TPIDR* registers */
	ldp	x19, x20, [x1, #RMM_TPIDR_EL0_OFFSET]
	msr	tpidr_el0, x19
	msr	tpidrro_el0, x20

	/* restore original vbar_el2 */
	ldr	x2, [x1, #RMM_VBAR_EL2_OFFSET]
	msr	vbar_el2, x2
	isb

	/* restore TTBR register */
	ldr	x2, [x1, #RMM_TTBR1_EL2_OFFSET]
	msr	ttbr1_el2, x2

	mrs	x2, tcr_el2
	and	x2, x2, #(~TCR_EL2_E0PD1) /* TODO: restore original value instead!!! */
	msr	tcr_el2, x2
	isb

	/*
	 * Restore the RMM registers from the stack
	 * including the return address to return to
	 * after calling run_app().
	 */
	ldp	x19, x20, [sp, #(16 * 0)]
	ldp	x21, x22, [sp, #(16 * 1)]
	ldp	x23, x24, [sp, #(16 * 2)]
	ldp	x25, x26, [sp, #(16 * 3)]
	ldp	x27, x28, [sp, #(16 * 4)]
	ldp	x29, x30, [sp, #(16 * 5)]
	add	sp, sp, #(16 * 6)

	ret

endfunc back_from_el0

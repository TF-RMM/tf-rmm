/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <asm_macros.S>

	.section ".text"

	.macro ventry_unused error_message
	.balign	0x80
	wfe
	b	.-4
	.endm

	.macro ventry label
		.balign	0x80
		b	\label
	.endm

	// VBAR_EL3[10:0] are hardwired to 0, align vector address accordingly
	.balign 0x800

ENTRY(el2_vectors):
	ventry_unused	exc_sync_sp0
	ventry_unused	exc_irq_sp0
	ventry_unused	exc_fiq_sp0
	ventry_unused	exc_serror_sp0

	ventry		el2_sync_cel
	ventry_unused	exc_irq_spx
	ventry_unused	exc_fiq_spx
	ventry_unused	exc_serror_spx

	ventry		el2_sync_lel
	ventry		el2_irq_lel
	ventry		el2_fiq_lel
	ventry		el2_serror_lel

	ventry_unused	exc_sync_lel_32
	ventry_unused	exc_irq_lel_32
	ventry_unused	exc_fiq_lel_32
	ventry_unused	exc_serror_lel_32
ENDPROC(el2_vectors)

el2_sync_lel:
	stp	x0, x1, [sp, #-16]!
	mov	x0, #ARM_EXCEPTION_SYNC_LEL
	b	realm_exit
ENDPROC(el2_sync_lel)

el2_irq_lel:
	stp	x0, x1, [sp, #-16]!
	mov	x0, #ARM_EXCEPTION_IRQ_LEL
	b	realm_exit
ENDPROC(el2_sync_lel)

el2_fiq_lel:
	stp	x0, x1, [sp, #-16]!
	mov	x0, #ARM_EXCEPTION_FIQ_LEL
	b	realm_exit
ENDPROC(el2_sync_lel)

el2_serror_lel:
	stp	x0, x1, [sp, #-16]!
	mov	x0, #ARM_EXCEPTION_SERROR_LEL
	b	realm_exit
ENDPROC(el2_serror_lel)

el2_sync_cel:

	/* Switch to exception handler stack */
	msr	spsel, #0

	stp	x0, x1, [sp, #-16]!
	stp	x2, x3, [sp, #-16]!
	stp	x4, x5, [sp, #-16]!
	stp	x6, x7, [sp, #-16]!
	stp	x8, x9, [sp, #-16]!
	stp	x10, x11, [sp, #-16]!
	stp	x12, x13, [sp, #-16]!
	stp	x14, x15, [sp, #-16]!
	stp	x16, x17, [sp, #-16]!
	stp	x18, xzr, [sp, #-16]!
	stp	x29, lr, [sp, #-16]!

	bl	handle_rmm_trap

	/*
	 * If it doesn't panic the RMM, handle_rmm_trap
	 * returns the new value of PC in x0.
	 */
	msr	elr_el2, x0

	ldp	x29, lr, [sp], #16
	ldp	x18, xzr, [sp], #16
	ldp	x16, x17, [sp], #16
	ldp	x14, x15, [sp], #16
	ldp	x12, x13, [sp], #16
	ldp	x10, x11, [sp], #16
	ldp	x8, x9, [sp], #16
	ldp	x6, x7, [sp], #16
	ldp	x4, x5, [sp], #16
	ldp	x2, x3, [sp], #16
	ldp	x0, x1, [sp], #16

	/* Switch back to normal stack */
	msr	spsel, #1

	eret
	sb

ENDPROC(el2_sync_cel)

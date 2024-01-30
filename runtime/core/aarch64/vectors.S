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
	msr	spsel, #MODE_SP_EL0

	/*
	 * Push registers to the crash dump structure
	 *
	 * typedef struct {
	 *	uint64_t x[30];
	 *	uint64_t lr;
	 * } dump_regs_t;
	 *
	 */
	stp	x29, x30, [sp, #-16]!
	stp	x27, x28, [sp, #-16]!
	stp	x25, x26, [sp, #-16]!
	stp	x23, x24, [sp, #-16]!
	stp	x21, x22, [sp, #-16]!
	stp	x19, x20, [sp, #-16]!
	stp	x17, x18, [sp, #-16]!
	stp	x15, x16, [sp, #-16]!
	stp	x13, x14, [sp, #-16]!
	stp	x11, x12, [sp, #-16]!
	stp	x9, x10, [sp, #-16]!
	stp	x7, x8, [sp, #-16]!
	stp	x5, x6, [sp, #-16]!
	stp	x3, x4, [sp, #-16]!
	stp	x1, x2, [sp, #-16]!
	stp	xzr, x0, [sp, #-16]!

	/* X0 points to the start of the structure */
	add	x0, sp, #8
	bl	handle_rmm_trap

	/*
	 * If it doesn't panic the RMM, handle_rmm_trap
	 * returns the new value of PC in x0.
	 */
	msr	elr_el2, x0

	ldp	xzr, x0, [sp], #16
	ldp	x1, x2, [sp], #16
	ldp	x3, x4, [sp], #16
	ldp	x5, x6, [sp], #16
	ldp	x7, x8, [sp], #16
	ldp	x9, x10, [sp], #16
	ldp	x11, x12, [sp], #16
	ldp	x13, x14, [sp], #16
	ldp	x15, x16, [sp], #16
	ldp	x17, x18, [sp], #16
	ldp	x19, x20, [sp], #16
	ldp	x21, x22, [sp], #16
	ldp	x23, x24, [sp], #16
	ldp	x25, x26, [sp], #16
	ldp	x27, x28, [sp], #16
	ldp	x29, x30, [sp], #16

	/* Switch back to normal stack */
	msr	spsel, #MODE_SP_ELX

	eret
	sb

ENDPROC(el2_sync_cel)

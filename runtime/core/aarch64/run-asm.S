/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <asm_macros.S>
#include <rec.h>
#include <xlat_high_va.h>

.globl run_realm
.globl realm_exit

/*
 * int run_realm(unsigned long *regs);
 *
 * Per the AAPCS we must preserve x19-x29, along with the SP. We may freely
 * corrupt x0-18 and the flags, but need the LR to return to our caller.
 */
func run_realm
	/* Push RMM registers to the stack */
	sub	sp, sp, #(16 * 6)
	stp	x19, x20, [sp, #(16 * 0)]
	stp	x21, x22, [sp, #(16 * 1)]
	stp	x23, x24, [sp, #(16 * 2)]
	stp	x25, x26, [sp, #(16 * 3)]
	stp	x27, x28, [sp, #(16 * 4)]
	stp	x29, x30, [sp, #(16 * 5)]

	/* Push rec pointer to the stack for realm_exit */
	stp	x0, xzr, [sp, #-16]!

	/* load realm GPRs (offsetof(rec, rec->regs[0]) == 0) */
	ldp	x2,  x3,  [x0, #(16 * 1)]
	ldp	x4,  x5,  [x0, #(16 * 2)]
	ldp	x6,  x7,  [x0, #(16 * 3)]
	ldp	x8,  x9,  [x0, #(16 * 4)]
	ldp	x10, x11, [x0, #(16 * 5)]
	ldp	x12, x13, [x0, #(16 * 6)]
	ldp	x14, x15, [x0, #(16 * 7)]
	ldp	x16, x17, [x0, #(16 * 8)]
	ldp	x18, x19, [x0, #(16 * 9)]
	ldp	x20, x21, [x0, #(16 * 10)]
	ldp	x22, x23, [x0, #(16 * 11)]
	ldp	x24, x25, [x0, #(16 * 12)]
	ldp	x26, x27, [x0, #(16 * 13)]
	ldp	x28, x29, [x0, #(16 * 14)]
	ldr	x30,      [x0, #(16 * 15)]
	ldr	x1,       [x0, #(16 * 15 + 8)]
	msr	sp_el0, x1
	ldp	x0,  x1,  [x0, #(16 * 0)]

	eret
	sb
endfunc run_realm

func realm_exit
	/*
	 * We come here with realm's x0 and x1 on the stack and exit_reason in
	 * x0. See el2_vectors in runtime/core/aarch64/vectors.S.
	 *
	 * First, restore realm_gprs ptr to x1
	 */

	/* Recover the rec pointer */
	ldr	x1, [sp, #16]

	/* Store realm GPRs (offsetof(rec, rec->regs[0]) == 0) */
	stp	x2,  x3,  [x1, #(16 * 1)]
	stp	x4,  x5,  [x1, #(16 * 2)]
	stp	x6,  x7,  [x1, #(16 * 3)]
	stp	x8,  x9,  [x1, #(16 * 4)]
	stp	x10, x11, [x1, #(16 * 5)]
	stp	x12, x13, [x1, #(16 * 6)]
	stp	x14, x15, [x1, #(16 * 7)]
	stp	x16, x17, [x1, #(16 * 8)]
	stp	x18, x19, [x1, #(16 * 9)]
	stp	x20, x21, [x1, #(16 * 10)]
	stp	x22, x23, [x1, #(16 * 11)]
	stp	x24, x25, [x1, #(16 * 12)]
	stp	x26, x27, [x1, #(16 * 13)]
	stp	x28, x29, [x1, #(16 * 14)]
	str	x30,      [x1, #(16 * 15)]
	mrs	x2, sp_el0
	str	x2,       [x1, #(16 * 15 + 8)]

	/* Load the exception handler stack bottom to SP_EL0 */
	mov_imm	x2, RMM_CPU_EH_STACK_END_VA
	msr	sp_el0, x2

	/* Disable DIT on return from Realm EL1/0 */
	msr	DIT, xzr

	/* x0 and x1 as stored by el2_vectors */
	ldp	x2, x3,	  [sp]
	stp	x2, x3,   [x1, #(16 * 0)]

	/* Move sp to the realm regs */
	add	sp, sp, #32

	/*
	 * Restore the RMM registers from the stack
	 * including the return address to return to
	 * after calling run_realm().
	 */
	ldp	x19, x20, [sp, #(16 * 0)]
	ldp	x21, x22, [sp, #(16 * 1)]
	ldp	x23, x24, [sp, #(16 * 2)]
	ldp	x25, x26, [sp, #(16 * 3)]
	ldp	x27, x28, [sp, #(16 * 4)]
	ldp	x29, x30, [sp, #(16 * 5)]
	add	sp, sp, #(16 * 6)

	ret
	sb
endfunc realm_exit

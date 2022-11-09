/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <asm_macros.S>

.globl fpu_save_state
.globl fpu_restore_state

/*
 * void fpu_save_state(struct fpu_state *fpu);
 *
 * This function saves the FPU state in systems supporting FPU but NOT SVE.
 * Systems with SVE support only use the SVE save/restore since these
 * registers are mapped into SVE registers.
 *
 * Since we make assumptions about register fields in C structs here, there are
 * compiler asserts in rec.h to help guarantee that these assumptions are true.
 */
func fpu_save_state
	/* Save the SIMD/FPU register bank to memory. */
	stp	q0, q1, [x0], #32
	stp	q2, q3, [x0], #32
	stp	q4, q5, [x0], #32
	stp	q6, q7, [x0], #32
	stp	q8, q9, [x0], #32
	stp	q10, q11, [x0], #32
	stp	q12, q13, [x0], #32
	stp	q14, q15, [x0], #32
	stp	q16, q17, [x0], #32
	stp	q18, q19, [x0], #32
	stp	q20, q21, [x0], #32
	stp	q22, q23, [x0], #32
	stp	q24, q25, [x0], #32
	stp	q26, q27, [x0], #32
	stp	q28, q29, [x0], #32
	stp	q30, q31, [x0], #32

	/* Save the FPSR/FPCR */
	mrs	x1, fpsr
	mrs	x2, fpcr
	stp	x1, x2, [x0]

	ret
endfunc fpu_save_state

/*
 * void fpu_restore_state(struct fpu_state *fpu);
 *
 * Function to restore a saved FPU register state on systems supporting FPU/SIMD
 * but NOT SVE.  Systems with SVE support enabled only use the SVE save/restore
 * since these registers are mapped into SVE registers.
 *
 * Since we make assumptions about register fields in C structs here, there are
 * compiler asserts in rec.h to help guarantee that these assumptions are true.
 */
func fpu_restore_state
	/* Load the SIMD/FPU register bank from memory. */
	ldp	q0, q1, [x0], #32
	ldp	q2, q3, [x0], #32
	ldp	q4, q5, [x0], #32
	ldp	q6, q7, [x0], #32
	ldp	q8, q9, [x0], #32
	ldp	q10, q11, [x0], #32
	ldp	q12, q13, [x0], #32
	ldp	q14, q15, [x0], #32
	ldp	q16, q17, [x0], #32
	ldp	q18, q19, [x0], #32
	ldp	q20, q21, [x0], #32
	ldp	q22, q23, [x0], #32
	ldp	q24, q25, [x0], #32
	ldp	q26, q27, [x0], #32
	ldp	q28, q29, [x0], #32
	ldp	q30, q31, [x0], #32

	/* Load the FPSR/FPCR */
	ldp	x1, x2, [x0]
	msr	fpsr, x1
	msr	fpcr, x2

	ret
endfunc fpu_restore_state

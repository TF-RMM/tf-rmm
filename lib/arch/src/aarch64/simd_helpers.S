/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <asm_macros.S>
#include <simd.h>

.globl fpu_save_registers
.globl fpu_restore_registers

.globl sve_rdvl
.globl sve_save_vector_registers
.globl sve_restore_vector_registers
.globl sve_clear_p_ffr_registers

/*
 * void fpu_save_registers(struct fpu_regs *regs);
 *
 * This function saves the FPU Q registers
 *
 * Inputs:
 *   x0 - address of fpu_regs
 * Clobbers:
 *   none
 * Returns:
 *   none
 */
func fpu_save_registers
.arch_extension fp
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

	ret
.arch_extension nofp
endfunc fpu_save_registers

/*
 * void fpu_restore_registers(struct fpu_regs *regs);
 *
 * Function to restore a saved FPU Q registers
 *
 * Inputs:
 *   x0 - address of fpu_regs
 * Clobbers:
 *   none
 * Returns:
 *   none
 */
func fpu_restore_registers
.arch_extension fp
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

	ret
.arch_extension nofp
endfunc fpu_restore_registers

/*
 * uint64_t sve_rdvl(void)
 *
 * Inputs:
 *   none
 * Returns:
 *   Return the length of one vector register in bytes
 */
func sve_rdvl
.arch_extension sve
	rdvl	x0, #1
	ret
.arch_extension nosve
endfunc sve_rdvl

/*
 * void sve_save_vector_registers(struct sve_regs *regs, bool save_ffr)
 *
 * The fields in 'struct sve_state' are accessed using OFFSET macros defined in
 * simd.h. There are compiler asserts in simd.h to help guarantee that these
 * values matches with the offset in 'struct sve_regs'.
 *
 * Inputs:
 *   x0 - address of sve_regs
 *   x1 - when non-zero, save FFR
 * Clobbers:
 *   x2
 * Returns:
 *   none
 */
func sve_save_vector_registers
.arch_extension sve
	mov	x2, x0

	/* Save the z register bank to memory. */
	mov	x0, #SVE_REGS_OFFSET_Z
	add	x0, x0, x2
	str	z0, [x0, #0, MUL VL]
	str	z1, [x0, #1, MUL VL]
	str	z2, [x0, #2, MUL VL]
	str	z3, [x0, #3, MUL VL]
	str	z4, [x0, #4, MUL VL]
	str	z5, [x0, #5, MUL VL]
	str	z6, [x0, #6, MUL VL]
	str	z7, [x0, #7, MUL VL]
	str	z8, [x0, #8, MUL VL]
	str	z9, [x0, #9, MUL VL]
	str	z10, [x0, #10, MUL VL]
	str	z11, [x0, #11, MUL VL]
	str	z12, [x0, #12, MUL VL]
	str	z13, [x0, #13, MUL VL]
	str	z14, [x0, #14, MUL VL]
	str	z15, [x0, #15, MUL VL]
	str	z16, [x0, #16, MUL VL]
	str	z17, [x0, #17, MUL VL]
	str	z18, [x0, #18, MUL VL]
	str	z19, [x0, #19, MUL VL]
	str	z20, [x0, #20, MUL VL]
	str	z21, [x0, #21, MUL VL]
	str	z22, [x0, #22, MUL VL]
	str	z23, [x0, #23, MUL VL]
	str	z24, [x0, #24, MUL VL]
	str	z25, [x0, #25, MUL VL]
	str	z26, [x0, #26, MUL VL]
	str	z27, [x0, #27, MUL VL]
	str	z28, [x0, #28, MUL VL]
	str	z29, [x0, #29, MUL VL]
	str	z30, [x0, #30, MUL VL]
	str	z31, [x0, #31, MUL VL]

	/* Save the P register bank to memory. */
	mov	x0, #SVE_REGS_OFFSET_P
	add	x0, x0, x2
	str 	p0, [x0, #0, MUL VL]
	str 	p1, [x0, #1, MUL VL]
	str 	p2, [x0, #2, MUL VL]
	str 	p3, [x0, #3, MUL VL]
	str 	p4, [x0, #4, MUL VL]
	str 	p5, [x0, #5, MUL VL]
	str 	p6, [x0, #6, MUL VL]
	str 	p7, [x0, #7, MUL VL]
	str 	p8, [x0, #8, MUL VL]
	str 	p9, [x0, #9, MUL VL]
	str 	p10, [x0, #10, MUL VL]
	str 	p11, [x0, #11, MUL VL]
	str 	p12, [x0, #12, MUL VL]
	str 	p13, [x0, #13, MUL VL]
	str 	p14, [x0, #14, MUL VL]
	str 	p15, [x0, #15, MUL VL]

	/* Save the ffr register, after predicates are saved. */
	cbz	x1, 1f
	mov	x0, #SVE_REGS_OFFSET_FFR
	add	x0, x0, x2
	rdffr	p0.B
	str 	p0, [x0, #0, MUL VL]
1:
	ret
.arch_extension nosve
endfunc sve_save_vector_registers

/*
 * void sve_restore_vector_registers(struct sve_regs *sve, bool restore_ffr)
 *
 * The fields in 'struct sve_state' are accessed using OFFSET macros defined in
 * simd.h. There are compiler asserts in simd.h to help guarantee that these
 * values matches with the offset in 'struct sve_state'.
 *
 * Inputs:
 *   x0 - address of sve_regs
 *   x1 - when non-zero, restore FFR
 * Clobbers:
 *   x2
 * Returns:
 *   none
 */
func sve_restore_vector_registers
.arch_extension sve
	mov	x2, x0

	/* Load the z register bank from memory. */
	mov	x0, #SVE_REGS_OFFSET_Z
	add	x0, x0, x2
	ldr 	z0, [x0, #0, MUL VL]
	ldr	z1, [x0, #1, MUL VL]
	ldr	z2, [x0, #2, MUL VL]
	ldr	z3, [x0, #3, MUL VL]
	ldr	z4, [x0, #4, MUL VL]
	ldr	z5, [x0, #5, MUL VL]
	ldr	z6, [x0, #6, MUL VL]
	ldr	z7, [x0, #7, MUL VL]
	ldr	z8, [x0, #8, MUL VL]
	ldr	z9, [x0, #9, MUL VL]
	ldr	z10, [x0, #10, MUL VL]
	ldr	z11, [x0, #11, MUL VL]
	ldr	z12, [x0, #12, MUL VL]
	ldr	z13, [x0, #13, MUL VL]
	ldr	z14, [x0, #14, MUL VL]
	ldr	z15, [x0, #15, MUL VL]
	ldr	z16, [x0, #16, MUL VL]
	ldr	z17, [x0, #17, MUL VL]
	ldr	z18, [x0, #18, MUL VL]
	ldr	z19, [x0, #19, MUL VL]
	ldr	z20, [x0, #20, MUL VL]
	ldr	z21, [x0, #21, MUL VL]
	ldr	z22, [x0, #22, MUL VL]
	ldr	z23, [x0, #23, MUL VL]
	ldr	z24, [x0, #24, MUL VL]
	ldr	z25, [x0, #25, MUL VL]
	ldr	z26, [x0, #26, MUL VL]
	ldr	z27, [x0, #27, MUL VL]
	ldr	z28, [x0, #28, MUL VL]
	ldr	z29, [x0, #29, MUL VL]
	ldr	z30, [x0, #30, MUL VL]
	ldr	z31, [x0, #31, MUL VL]

	/* Restore the ffr register before restoring predicates */
	cbz	x1, 1f
	mov	x0, #SVE_REGS_OFFSET_FFR
	add	x0, x0, x2
	ldr 	p0, [x0, #0, MUL VL]
	wrffr	p0.B
1:

	/* Load the P register bank from memory. */
	mov	x0, #SVE_REGS_OFFSET_P
	add	x0, x0, x2
	ldr 	p0, [x0, #0, MUL VL]
	ldr 	p1, [x0, #1, MUL VL]
	ldr 	p2, [x0, #2, MUL VL]
	ldr 	p3, [x0, #3, MUL VL]
	ldr 	p4, [x0, #4, MUL VL]
	ldr 	p5, [x0, #5, MUL VL]
	ldr 	p6, [x0, #6, MUL VL]
	ldr 	p7, [x0, #7, MUL VL]
	ldr 	p8, [x0, #8, MUL VL]
	ldr 	p9, [x0, #9, MUL VL]
	ldr 	p10, [x0, #10, MUL VL]
	ldr 	p11, [x0, #11, MUL VL]
	ldr 	p12, [x0, #12, MUL VL]
	ldr 	p13, [x0, #13, MUL VL]
	ldr 	p14, [x0, #14, MUL VL]
	ldr 	p15, [x0, #15, MUL VL]

	ret
.arch_extension nosve
endfunc sve_restore_vector_registers

/*
 * void sve_clear_p_ffr_registers(void)
 *
 * Clear SVE P and FFR registers.
 *
 * Returns:
 *   none
 */
func sve_clear_p_ffr_registers
.arch_extension sve
	pfalse	p0.B
	pfalse	p1.B
	pfalse	p2.B
	pfalse	p3.B
	pfalse	p4.B
	pfalse	p5.B
	pfalse	p6.B
	pfalse	p7.B
	pfalse	p8.B
	pfalse	p9.B
	pfalse	p10.B
	pfalse	p11.B
	pfalse	p12.B
	pfalse	p13.B
	pfalse	p14.B
	pfalse	p15.B

	wrffr	p0.B
	ret
.arch_extension nosve
endfunc sve_clear_p_ffr_registers

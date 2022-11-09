/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <asm_macros.S>
#include <smc.h>

.globl rmm_handler

func rmm_handler
	/*
	 * Save Link Register and X4, as per SMCCC v1.2 its value
	 * must be preserved unless it contains result, as specified
	 * in the function definition.
	 */
	stp	x4, lr, [sp, #-16]!

	/*
	 * Zero the space for X0-X3 in the smc_result structure
	 * and pass its address as the last argument.
	 */
	stp	xzr, xzr, [sp, #-16]!
	stp	xzr, xzr, [sp, #-16]!
	mov	x7, sp

	bl	handle_ns_smc

	/*
	 * Copy command output values back to caller. Since this is
	 * done through SMC, X0 is used as the FID, and X1-X5 contain
	 * the values of X0-X4 copied from the smc_result structure.
	 */
	ldr	x0, =SMC_RMM_REQ_COMPLETE
	ldp	x1, x2, [sp], #16
	ldp	x3, x4, [sp], #16
	ldp	x5, lr, [sp], #16

	smc	#0

	/* Continue the rmm handling loop */
	b	rmm_handler
endfunc rmm_handler

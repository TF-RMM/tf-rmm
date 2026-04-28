/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <asm_macros.S>
#include <smc.h>

/* Size of the frame header: [sp+0] res pointer + [sp+8] saved LR */
#define LR_AND_RES_PTR_SIZE	16

.globl rmm_handler

func rmm_handler
	/*
	 * Allocate (LR_AND_RES_PTR_SIZE + SMC_RESULT_SIZE) bytes on the stack. Layout:
	 *   [sp+ 0]: res pointer (9th arg to handle_ns_smc, it points to 'sp+LR_AND_RES_PTR_SIZE')
	 *   [sp+ 8]: saved LR
	 *   [sp+16]: smc_result->x[0]  (returned via X1)
	 *   [sp+24]: smc_result->x[1]  (returned via X2)
	 *   [sp+32]: smc_result->x[2]  (returned via X3)
	 *   [sp+40]: smc_result->x[3]  (returned via X4)
	 *   [sp+48]: smc_result->x[4]  (returned via X5, init: saved X4)
	 *   [sp+56]: smc_result->x[5]  (returned via X6, init: saved X5)
	 *   [sp+64]: smc_result->x[6]  (returned via X7, init: saved X6)
	 *   [sp+72]: smc_result->x[7]  (returned via X8, init: saved X7)
	 *
	 * X4-X7 are pre-loaded into smc_result->x[4..7] so that per SMCCC
	 * v1.2 their values are preserved if not written as output by the
	 * handler.
	 */
	sub	sp, sp, #(LR_AND_RES_PTR_SIZE + SMC_RESULT_SIZE)

	/* Save LR */
	str	lr, [sp, #8]

	/* Save X4-X7 into smc_result->x[4..7] slots */
	stp	x4, x5, [sp, #(LR_AND_RES_PTR_SIZE + SMC_RES_X4_X5)]
	stp	x6, x7, [sp, #(LR_AND_RES_PTR_SIZE + SMC_RES_X6_X7)]

	/*
	 * smc_result->x[0..3] is zeroed in handle_ns_smc() so that both
	 * AArch64 and fake_host paths behave identically.
	 */

	/*
	 * Store the res pointer (sp+LR_AND_RES_PTR_SIZE) as the 9th stack argument.
	 * X0-X7 already carry function_id and arg0-arg6 unchanged.
	 */
	add	x8, sp, #(LR_AND_RES_PTR_SIZE)
	str	x8, [sp, #0]

	bl	handle_ns_smc

	/*
	 * Copy command output values back to caller. Since this is
	 * done through SMC, X0 is used as the FID, and X1-X8 contain
	 * the values of X0-X7 copied from the smc_result structure.
	 */
	ldr	x0, =SMC_RMM_REQ_COMPLETE
	ldp	x1, x2, [sp, #(LR_AND_RES_PTR_SIZE + SMC_RES_X0_X1)]
	ldp	x3, x4, [sp, #(LR_AND_RES_PTR_SIZE + SMC_RES_X2_X3)]
	ldp	x5, x6, [sp, #(LR_AND_RES_PTR_SIZE + SMC_RES_X4_X5)]
	ldp	x7, x8, [sp, #(LR_AND_RES_PTR_SIZE + SMC_RES_X6_X7)]
	ldr	lr, [sp, #8]
	add	sp, sp, #(LR_AND_RES_PTR_SIZE + SMC_RESULT_SIZE)

	smc	#0

	/* Continue the rmm handling loop */
	b	rmm_handler
endfunc rmm_handler

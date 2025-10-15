/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <asm_macros.S>
#include <smc.h>

.globl monitor_call
.globl monitor_call_with_arg_res

func monitor_call
	/* As this is a function call, the arguments must already be in
	 * place in accordance to SMCCC.
	 */
	smc #0
	ret
endfunc monitor_call

/*
 * This is a function call to invoke SMC with the extended arguments passed
 * using smc_arg
 *
 * Arguments:
 *    x0 - SMC function ID
 *    x1 - smc_arg extended argument list
 *    x2 - Reference to smc_result structure allocated by caller
 * Return:
 *    x0 - Return value from SMC
 */
func monitor_call_with_arg_res
	/*
	 * Push the value of x2 to the stack, as the SMC might change the
	 * content. (push two registers to maintain 16 bit aligned stack)
	 */
	stp x2, x3, [sp, #-16]!
	/* Load the arguments to registers */
	ldp x11, x12, [x1, #SMC_ARG_X11_X12]
	ldp x9, x10, [x1, #SMC_ARG_X9_X10]
	ldp x7, x8, [x1, #SMC_ARG_X7_X8]
	ldp x5, x6, [x1, #SMC_ARG_X5_X6]
	ldp x3, x4, [x1, #SMC_ARG_X3_X4]
	ldp x1, x2, [x1, #SMC_ARG_X1_X2]
	/* Call SMC */
	smc #0
	/*
	 * Pop the saved values from stack. We are loading the values to
	 * registers that are not used for return vales
	 */
	ldp x11, x12, [sp], #16
	/* Fill the smc_result structure */
	stp x0, x1, [x11, #SMC_RES_X0_X1]
	stp x2, x3, [x11, #SMC_RES_X2_X3]
	str x4, [x11, #SMC_RES_X4]
	ret
endfunc monitor_call_with_arg_res

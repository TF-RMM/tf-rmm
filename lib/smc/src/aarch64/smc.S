/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <asm_macros.S>

.globl monitor_call
.globl monitor_call_with_res

func monitor_call
	/* As this is a function call, the arguments must already be in
	 * place in accordance to SMCCC.
	 */
	smc #0
	ret
endfunc monitor_call

/*
 * Issue an SMC call to EL3 monitor with the ability to return more than 1
 * result register.
 * The arguments to this function are :
 *    x0 - x6 - SMC call arguments
 *    x7 - Reference to smc_result structure allocated by caller
 * Return :
 *    x0 - x3 Return values from SMC
 * The return args are also copied to smc_result data structure.
 */
func monitor_call_with_res
	/*
	 * Push the value of x7 to the stack, as the SMC might change the
	 * content. (push two registers to maintain 16 bit aligned stack)
	 */
	stp x7, x8, [sp, #-16]!
	/* Call SMC */
	smc #0
	/* Pop the saved values from stack */
	ldp x7, x8, [sp], #16
	/* Fill the smc_result structure */
	stp x0, x1, [x7, #0]
	stp x2, x3, [x7, #16]
	ret
endfunc monitor_call_with_res

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <asm_macros.S>
#include <xlat_defs.h>
#include <xlat_high_va.h>

.globl rmm_get_my_eh_stack
.globl rmm_get_my_stack

 /*
 * Return the stack for exception handler for a given PE index in x0
 * rmm_eh_stack_start			     rmm_eh_stack_end
 *       o--sz---o....o--sz---o--sz---o--sz---o
 *       ^\_____/^....^\_____/^\_____/^\_____/^
 * id = (MAX_CPU-1)      2       1       0
 * Arg : x0 - CPU position
 * sz: RMM_CPU_EH_STACK_SIZE bytes.
 */
func rmm_get_my_eh_stack
#ifndef NDEBUG
	cmp	x0, #MAX_CPUS
	ASM_ASSERT lo
#endif
	adrp	x1, rmm_eh_stack_end
	add	x1, x1, :lo12:rmm_eh_stack_end
	mov_imm	x2, RMM_CPU_EH_STACK_SIZE	/* Exception handler stack size per CPU */
	umsubl	x0, w0, w2, x1
	ret
endfunc rmm_get_my_eh_stack

 /*
 * Return the stack for a given PE index in x0
 * stack-start				     rmm_stack_end
 *       o--sz---o....o--sz---o--sz---o--sz---o
 *       ^\_____/^....^\_____/^\_____/^\_____/^
 * id = (MAX_CPU-1)      2       1       0
 * Arg : x0 - CPU position
 * sz: RMM_CPU_STACK_SIZE bytes.
 */
func rmm_get_my_stack
#ifndef NDEBUG
	cmp	x0, #MAX_CPUS
	ASM_ASSERT lo
#endif
	adrp	x1, rmm_stack_end
	add	x1, x1, :lo12:rmm_stack_end
	mov_imm	x2, RMM_CPU_STACK_SIZE	/* stack size per CPU */
	umsubl	x0, w0, w2, x1
	ret
endfunc rmm_get_my_stack

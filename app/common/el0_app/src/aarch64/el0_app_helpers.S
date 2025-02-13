/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_common.h>
#include <asm_macros.S>

.globl el0_app_entry
.globl el0_app_service_call

/*
 * This function must be the first function in the file!
 * This function is the entry point, linked to be the first in the .text
 * section.
 */
func el0_app_entry
	mov	x20, x0
	mov	x21, x1
	mov	x22, x2
	mov	x23, x3
	mov	x24, x4
	mov	x25, lr
	bl init_console
	mov	x0, x20
	mov	x1, x21
	mov	x2, x22
	mov	x3, x23
	mov	x4, x24
	mov	lr, x25
app_loop:
	bl el0_app_entry_func
	svc APP_EXIT_CALL
	b app_loop
endfunc el0_app_entry

func el0_app_service_call
	svc APP_SERVICE_CALL
	ret
endfunc el0_app_service_call



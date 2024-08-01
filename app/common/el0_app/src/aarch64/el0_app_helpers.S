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
	bl el0_app_entry_func
	svc APP_EXIT_CALL
	b el0_app_entry
endfunc el0_app_entry

func el0_app_service_call
	svc APP_SERVICE_CALL
	ret
endfunc el0_app_service_call



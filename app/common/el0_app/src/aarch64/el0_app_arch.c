/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <debug.h>
#include <el0_app_helpers.h>
#include <import_sym.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>

IMPORT_SYM(uintptr_t, el0_app_shared_start, EL0_APP_SHARED_START);
IMPORT_SYM(uintptr_t, el0_app_shared_end, EL0_APP_SHARED_END);

/* Logging for RMM EL0 apps */
void rmm_log(const char *fmt, ...)
{
	va_list args;

	va_start(args, fmt);
	(void)vprintf(fmt, args);
	va_end(args);

	/* Tell the service call to flush the buffered message */
	(void)el0_app_service_call(APP_SERVICE_PRINT, 0U, 1U, 0U, 0U);
}

void *get_shared_mem_start(void)
{
	return (void *)EL0_APP_SHARED_START;
}

size_t get_shared_mem_size(void)
{
	return EL0_APP_SHARED_END - EL0_APP_SHARED_START;
}

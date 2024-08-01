/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <el0_app_helpers.h>
#include <import_sym.h>
#include <stdint.h>

IMPORT_SYM(uintptr_t, el0_app_shared_start, EL0_APP_SHARED_START);
IMPORT_SYM(uintptr_t, el0_app_shared_end, EL0_APP_SHARED_END);

void *get_shared_mem_start(void)
{
	return (void *)EL0_APP_SHARED_START;
}

size_t get_shared_mem_size(void)
{
	return EL0_APP_SHARED_END - EL0_APP_SHARED_START;
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <xlat_high_va.h>

uintptr_t rmm_get_my_stack(unsigned long cpuid)
{
	(void)cpuid;
	return 0x10000UL;
}

uintptr_t rmm_get_my_eh_stack(unsigned long cpuid)
{
	(void)cpuid;
	return 0x20000UL;
}

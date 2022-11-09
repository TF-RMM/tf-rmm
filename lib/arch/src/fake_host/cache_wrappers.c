/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>

/*******************************************************************************
 * Cache management
 ******************************************************************************/
void flush_dcache_range(uintptr_t addr, size_t size)
{
	(void)addr;
	(void)size;
}
void clean_dcache_range(uintptr_t addr, size_t size)
{
	(void)addr;
	(void)size;
}
void inv_dcache_range(uintptr_t addr, size_t size)
{
	(void)addr;
	(void)size;
}

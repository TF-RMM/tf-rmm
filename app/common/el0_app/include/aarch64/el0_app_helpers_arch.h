/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef EL0_APP_HELPERS_ARCH_H
#define EL0_APP_HELPERS_ARCH_H

#include <app_common.h>
#include <arch_helpers.h>

__unused static void *get_heap_start(void)
{
	uint64_t heap_properties = read_tpidrro_el0();

	return  (void *)(heap_properties & HEAP_VA_MASK);
}

__unused static size_t get_heap_size(void)
{
	uint64_t heap_properties = read_tpidrro_el0();

	return  (heap_properties & HEAP_PAGE_COUNT_MASK) * GRANULE_SIZE;
}

#endif /* EL0_APP_HELPERS_ARCH_H */


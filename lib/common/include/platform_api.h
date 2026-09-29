/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PLATFORM_API_H
#define PLATFORM_API_H

#include <smc-rmi.h>
#include <stdint.h>

struct plat_memory_bank {
	unsigned long base;
	unsigned long size;
};

void plat_warmboot_setup(uint64_t x0, uint64_t x1, uint64_t x2, uint64_t x3);
void plat_setup(uint64_t x0, uint64_t x1, uint64_t x2, uint64_t x3, uint64_t x4);

/*
 * Returns the platform-owned static memory bank array for the RMI memory
 * @category and writes its number of entries to @num_banks. The array is
 * ordered by address and remains valid after this function returns. The caller
 * must not modify it. Returns NULL for an invalid category or a NULL
 * @num_banks.
 */
const struct plat_memory_bank *plat_get_mem_banks(
					unsigned long category,
					unsigned long *num_banks);

#endif /* PLATFORM_API_H */

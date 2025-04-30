/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#ifndef PLATFORM_API_H
#define PLATFORM_API_H

#include <dev_type.h>
#include <stdint.h>

void plat_warmboot_setup(uint64_t x0, uint64_t x1, uint64_t x2, uint64_t x3);
void plat_setup(uint64_t x0, uint64_t x1, uint64_t x2, uint64_t x3);

/*
 * Takes an aligned granule address, validates it and if valid returns the
 * index in the struct granules array or UINT64_MAX in case of an error.
 *
 * This function also validates that the granule address is a valid
 * page address.
 */
unsigned long plat_granule_addr_to_idx(unsigned long addr);

/*
 * Takes an aligned dev_granule address, validates it and if valid returns the
 * index in the struct dev_granules array or UINT64_MAX in case of an error.
 *
 * This function also validates that the dev_granule address is a valid page
 * address and returns device granule coherency type if the addr is valid.
 */
unsigned long plat_dev_granule_addr_to_idx(unsigned long addr, enum dev_coh_type *type);

/*
 * Takes an index in the struct granules array and returns the aligned granule
 * address. The index must be within the number of granules expected by the
 * platform.
 */
unsigned long plat_granule_idx_to_addr(unsigned long idx);

/*
 * Takes an index in the struct dev_granules array and returns the aligned
 * dev_granule address of the specified device type. The index must be within
 * the number of dev_granules expected by the platform.
 */
unsigned long plat_dev_granule_idx_to_addr(unsigned long idx, enum dev_coh_type type);

#endif /* PLATFORM_API_H */

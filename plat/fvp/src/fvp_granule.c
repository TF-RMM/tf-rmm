/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <fvp_private.h>
#include <utils_def.h>

COMPILER_ASSERT(RMM_MAX_GRANULES >= FVP_NR_GRANULES);

unsigned long plat_granule_addr_to_idx(unsigned long addr)
{
	if (!(GRANULE_ALIGNED(addr) &&
	   (((addr >= FVP_DRAM0_BASE) && (addr <= FVP_DRAM0_END)) ||
	    ((addr >= FVP_DRAM1_BASE) && (addr <= FVP_DRAM1_END))))) {
		return UINT64_MAX;
	}

	if (addr < FVP_DRAM1_BASE) {
		return (addr - FVP_DRAM0_BASE) / GRANULE_SIZE;
	}

	return ((addr - FVP_DRAM1_BASE) / GRANULE_SIZE) + FVP_DRAM1_IDX;
}

unsigned long plat_granule_idx_to_addr(unsigned long idx)
{
	assert(idx < FVP_NR_GRANULES);

	if (idx < FVP_DRAM1_IDX) {
		return FVP_DRAM0_BASE + (idx * GRANULE_SIZE);
	}

	return FVP_DRAM1_BASE + ((idx - FVP_DRAM1_IDX) * GRANULE_SIZE);
}

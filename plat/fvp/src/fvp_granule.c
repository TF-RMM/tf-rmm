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
				(addr < (FVP_DRAM0_BASE + FVP_DRAM0_SIZE))) &&
				(addr >= FVP_DRAM0_BASE)) {
		return UINT64_MAX;
	}

	return (addr - FVP_DRAM0_BASE) / GRANULE_SIZE;
}

unsigned long plat_granule_idx_to_addr(unsigned long idx)
{
	assert(idx < FVP_NR_GRANULES);
	return FVP_DRAM0_BASE + (idx * GRANULE_SIZE);
}

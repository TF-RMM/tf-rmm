/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <fvp_dram.h>
#include <platform_api.h>
#include <utils_def.h>

static struct fvp_dram_layout fvp_dram;

struct fvp_dram_layout *fvp_get_dram_layout(void)
{
	return &fvp_dram;
}

unsigned long plat_granule_addr_to_idx(unsigned long addr)
{
	if (!GRANULE_ALIGNED(addr)) {
		return UINT64_MAX;
	}

	if ((addr >= fvp_dram.fvp_bank[0].start_addr) &&
	    (addr <= fvp_dram.fvp_bank[0].end_addr)) {
		return (addr - fvp_dram.fvp_bank[0].start_addr) / GRANULE_SIZE;
	}

	if ((fvp_dram.fvp_bank[1].start_addr != 0UL) &&
	    (addr >= fvp_dram.fvp_bank[1].start_addr) &&
	    (addr <= fvp_dram.fvp_bank[1].end_addr)) {
		return ((addr - fvp_dram.fvp_bank[1].start_addr) /
			GRANULE_SIZE) + fvp_dram.idx_bank_1;
	}

	return UINT64_MAX;
}

unsigned long plat_granule_idx_to_addr(unsigned long idx)
{
	assert(idx < fvp_dram.num_granules);

	if (idx < fvp_dram.idx_bank_1) {
		return fvp_dram.fvp_bank[0].start_addr + (idx * GRANULE_SIZE);
	}

	return fvp_dram.fvp_bank[1].start_addr +
			((idx - fvp_dram.idx_bank_1) * GRANULE_SIZE);
}

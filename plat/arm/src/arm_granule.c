/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arm_dram.h>
#include <assert.h>
#include <platform_api.h>
#include <utils_def.h>

static struct arm_dram_layout arm_dram;

struct arm_dram_layout *arm_get_dram_layout(void)
{
	return &arm_dram;
}

unsigned long plat_granule_addr_to_idx(unsigned long addr)
{
	if (!GRANULE_ALIGNED(addr)) {
		return UINT64_MAX;
	}

	if ((addr >= arm_dram.arm_bank[0].start_addr) &&
	    (addr <= arm_dram.arm_bank[0].end_addr)) {
		return (addr - arm_dram.arm_bank[0].start_addr) / GRANULE_SIZE;
	}

	if ((arm_dram.arm_bank[1].start_addr != 0UL) &&
	    (addr >= arm_dram.arm_bank[1].start_addr) &&
	    (addr <= arm_dram.arm_bank[1].end_addr)) {
		return ((addr - arm_dram.arm_bank[1].start_addr) /
			GRANULE_SIZE) + arm_dram.idx_bank_1;
	}

	return UINT64_MAX;
}

unsigned long plat_granule_idx_to_addr(unsigned long idx)
{
	assert(idx < arm_dram.num_granules);

	if (idx < arm_dram.idx_bank_1) {
		return arm_dram.arm_bank[0].start_addr + (idx * GRANULE_SIZE);
	}

	return arm_dram.arm_bank[1].start_addr +
			((idx - arm_dram.idx_bank_1) * GRANULE_SIZE);
}

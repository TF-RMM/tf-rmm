/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <qemu_dram.h>
#include <qemu_private.h>
#include <utils_def.h>

static struct qemu_dram_layout qemu_dram;

struct qemu_dram_layout *qemu_get_dram_layout(void)
{
	return &qemu_dram;
}

unsigned long plat_granule_addr_to_idx(unsigned long addr)
{
	if (!GRANULE_ALIGNED(addr)) {
		return UINT64_MAX;
	}

	if ((addr >= qemu_dram.start_addr) &&
	    (addr <= qemu_dram.end_addr)) {
		return (addr - qemu_dram.start_addr) / GRANULE_SIZE;
	}

	return UINT64_MAX;
}

unsigned long plat_granule_idx_to_addr(unsigned long idx)
{
	assert(idx < qemu_dram.num_granules);

	return qemu_dram.start_addr + (idx * GRANULE_SIZE);
}

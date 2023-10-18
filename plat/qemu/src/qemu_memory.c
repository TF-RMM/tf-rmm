/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <qemu_dram.h>
#include <rmm_el3_ifc.h>

void qemu_set_dram_layout(struct ns_dram_info *plat_dram)
{
	uint64_t size;
	uintptr_t start;
	struct ns_dram_bank *bank_ptr;
	struct qemu_dram_layout *qemu_dram = qemu_get_dram_layout();

	assert(plat_dram->num_banks == 1);
	bank_ptr = plat_dram->banks;

	start = bank_ptr->base;
	size = bank_ptr->size;

	qemu_dram->start_addr = start;
	qemu_dram->end_addr = start + size - 1UL;
	qemu_dram->num_granules = size / GRANULE_SIZE;

	flush_dcache_range((uintptr_t)qemu_dram, sizeof(qemu_dram));
}

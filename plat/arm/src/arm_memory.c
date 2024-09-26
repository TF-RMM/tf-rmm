/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <arm_dram.h>
#include <assert.h>
#include <rmm_el3_ifc.h>

void arm_set_dram_layout(struct ns_dram_info *plat_dram)
{
	struct ns_dram_bank *bank_ptr;
	struct arm_dram_layout *dram_ptr = arm_get_dram_layout();
	uint64_t num_banks, num_granules;

	assert(!is_mmu_enabled());

	/* Number of banks */
	num_banks = plat_dram->num_banks;
	assert(num_banks > 0UL);
	assert(num_banks <= PLAT_ARM_MAX_DRAM_BANKS);

	/* Pointer to dram_bank[] array */
	bank_ptr = plat_dram->banks;

	num_granules = 0UL;

	for (unsigned long i = 0UL; i < num_banks; i++) {
		uint64_t base = bank_ptr->base;
		uint64_t size = bank_ptr->size;

		dram_ptr->bank[i].base = base;
		dram_ptr->bank[i].size = size;
		dram_ptr->bank[i].start_gran_idx = num_granules;

		num_granules += (size >> GRANULE_SHIFT);
		bank_ptr++;
	}

	assert(num_granules <= RMM_MAX_GRANULES);

	dram_ptr->num_banks = num_banks;
	dram_ptr->num_granules = num_granules;

	inv_dcache_range((uintptr_t)dram_ptr, sizeof(struct arm_dram_layout));
}

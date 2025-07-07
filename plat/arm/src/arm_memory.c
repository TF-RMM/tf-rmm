/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <arm_memory.h>
#include <assert.h>
#include <rmm_el3_ifc.h>

static void arm_set_memory_layout(struct memory_info *plat_info,
				  struct arm_memory_layout *memory_ptr)
{
	struct memory_bank *bank_ptr;
	uint64_t num_banks, num_granules = 0UL;

	assert((plat_info != NULL) && (memory_ptr != NULL));
	assert(!is_mmu_enabled());

	/* Number of banks */
	num_banks = plat_info->num_banks;
	assert(num_banks > 0UL);
	assert(num_banks <= PLAT_ARM_MAX_MEM_BANKS);

	/* Pointer to memory_bank[] array */
	assert(plat_info->banks != NULL);
	bank_ptr = plat_info->banks;

	for (unsigned long i = 0UL; i < num_banks; i++) {
		uint64_t base = bank_ptr->base;
		uint64_t size = bank_ptr->size;

		memory_ptr->bank[i].base = base;
		memory_ptr->bank[i].size = size;
		memory_ptr->bank[i].start_gran_idx = num_granules;

		num_granules += (size >> GRANULE_SHIFT);
		bank_ptr++;
	}

	memory_ptr->num_banks = num_banks;
	memory_ptr->num_granules = num_granules;

	inv_dcache_range((uintptr_t)memory_ptr,
				sizeof(struct arm_memory_layout));
}

void arm_set_dram_layout(struct memory_info *plat_dram)
{
	assert(plat_dram != NULL);
	arm_set_memory_layout(plat_dram, arm_get_dram_layout());
}

void arm_set_dev_layout(struct memory_info *plat_dev, enum dev_coh_type type)
{
	struct arm_memory_layout *memory_ptr;

	assert(plat_dev != NULL);
	assert(type < DEV_MEM_MAX);

	switch (type) {
	case DEV_MEM_COHERENT:
		memory_ptr = arm_get_dev_coh_layout();
		break;
	default:
		/* DEV_MEM_NON_COHERENT */
		memory_ptr = arm_get_dev_ncoh_layout();
	}

	arm_set_memory_layout(plat_dev, memory_ptr);
}

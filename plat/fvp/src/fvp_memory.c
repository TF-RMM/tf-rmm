/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <fvp_dram.h>
#include <rmm_el3_ifc.h>

COMPILER_ASSERT(MAX_DRAM_NUM_BANKS == 2UL);

void fvp_set_dram_layout(struct ns_dram_info *plat_dram)
{
	uint64_t num_banks, num_granules = 0UL;
	struct ns_dram_bank *bank_ptr;
	struct fvp_dram_layout *fvp_dram = fvp_get_dram_layout();

	/* Number of banks */
	num_banks = plat_dram->num_banks;
	assert(num_banks <= MAX_DRAM_NUM_BANKS);

	/* Pointer to dram_bank[] array */
	bank_ptr = plat_dram->banks;

	for (unsigned long i = 0UL; i < num_banks; i++) {
		uintptr_t start = bank_ptr->base;
		uint64_t size = bank_ptr->size;
		uintptr_t end = start + size - 1UL;

		if (i == 1UL) {
			/* Start granule index in bank 1 */
			fvp_dram->idx_bank_1 = num_granules;
		}

		/* Total number of granules */
		num_granules += (size / GRANULE_SIZE);

		fvp_dram->fvp_bank[i].start_addr = start;
		fvp_dram->fvp_bank[i].end_addr = end;

		bank_ptr++;
	}

	fvp_dram->num_granules = num_granules;

	flush_dcache_range((uintptr_t)fvp_dram, sizeof(struct fvp_dram_layout));
}

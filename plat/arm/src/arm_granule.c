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
	const struct arm_dram_layout *dram = &arm_dram;
	unsigned long r, l = 0UL;

	if (!GRANULE_ALIGNED(addr)) {
		return UINT64_MAX;
	}

	assert(dram->num_banks > 0UL);
	assert(dram->num_banks <= PLAT_ARM_MAX_DRAM_BANKS);
	r = dram->num_banks - 1UL;

	/*
	 * Use a binary search rather than a linear one to locate the bank which
	 * the address falls within, then use the start_gran_idx (which is a
	 * cumulative idx from previous dram banks) to calculate the required
	 * granule index.
	 */
	while (l <= r) {
		const struct arm_dram_bank *bank;
		unsigned long i;

		i = l + ((r - l) / 2UL);
		assert(i < PLAT_ARM_MAX_DRAM_BANKS);

		bank = &dram->bank[i];

		if (addr < bank->base) {
			if (i == 0UL) {
				break;
			}
			r = i - 1UL;
		} else if (addr > (bank->base + bank->size - 1UL)) {
			l = i + 1UL;
		} else {
			return (bank->start_gran_idx +
			      ((addr - bank->base) >> GRANULE_SHIFT));
		}
	}
	return UINT64_MAX;
}

unsigned long plat_granule_idx_to_addr(unsigned long idx)
{
	const struct arm_dram_layout *dram = &arm_dram;
	unsigned long r, l = 0UL, addr = 0UL;

	assert(dram->num_banks > 0UL);
	assert(idx < dram->num_granules);

	r = dram->num_banks - 1UL;

	/*
	 * Calculate the start and end granule index of each bank using the
	 * start_gran_idx (which is a cumulative idx from previous dram banks)
	 * and then check whether the given index falls within it.
	 */
	while (l <= r) {
		const struct arm_dram_bank *bank;
		unsigned long i;
		unsigned long idx_start, idx_end;

		i = l + ((r - l) / 2UL);
		assert(i < PLAT_ARM_MAX_DRAM_BANKS);

		bank = &dram->bank[i];

		idx_start = bank->start_gran_idx;
		idx_end = idx_start + (bank->size >> GRANULE_SHIFT) - 1UL;

		if (idx < idx_start) {
			assert(i != 0UL);
			r = i - 1UL;
		} else if (idx > idx_end) {
			l = i + 1UL;
		} else {
			addr = bank->base + ((idx - idx_start) << GRANULE_SHIFT);
			break;
		}
	}
	/* Assert that the search was successful */
	assert(l <= r);
	return addr;
}

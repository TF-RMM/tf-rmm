/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arm_memory.h>
#include <assert.h>
#include <platform_api.h>
#include <utils_def.h>

static struct arm_memory_layout arm_dram;
static struct arm_memory_layout arm_dev_ncoh;
static struct arm_memory_layout arm_dev_coh;

/* cppcheck-suppress misra-c2012-8.7 */
struct arm_memory_layout *arm_get_dram_layout(void)
{
	return &arm_dram;
}

/* cppcheck-suppress misra-c2012-8.7 */
struct arm_memory_layout *arm_get_dev_ncoh_layout(void)
{
	return &arm_dev_ncoh;
}

/* cppcheck-suppress misra-c2012-8.7 */
struct arm_memory_layout *arm_get_dev_coh_layout(void)
{
	return &arm_dev_coh;
}

static unsigned long granule_addr_to_idx(unsigned long addr,
					 struct arm_memory_layout *memory_ptr)
{
	unsigned long r, l = 0UL;

	if (!GRANULE_ALIGNED(addr) || (memory_ptr->num_banks == 0UL)) {
		return UINT64_MAX;
	}

	assert(memory_ptr->num_banks <= PLAT_ARM_MAX_MEM_BANKS);
	r = memory_ptr->num_banks - 1UL;

	/*
	 * Use a binary search rather than a linear one to locate the bank which
	 * the address falls within, then use the start_gran_idx (which is a
	 * cumulative idx from previous memory banks) to calculate the required
	 * granule index.
	 */
	while (l <= r) {
		const struct arm_memory_bank *bank;
		unsigned long i;

		i = l + ((r - l) / 2UL);
		assert(i < PLAT_ARM_MAX_MEM_BANKS);

		bank = &memory_ptr->bank[i];

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

/* cppcheck-suppress misra-c2012-8.7 */
unsigned long plat_granule_addr_to_idx(unsigned long addr)
{
	return granule_addr_to_idx(addr, &arm_dram);
}

unsigned long plat_dev_granule_addr_to_idx(unsigned long addr, enum dev_coh_type *type)
{
	unsigned long ret;

	assert(type != NULL);

	/* Check non-coherent device granules */
	if (arm_dev_ncoh.num_granules != 0UL) {
		ret = granule_addr_to_idx(addr, &arm_dev_ncoh);
		if (ret != UINT64_MAX) {
			*type = DEV_MEM_NON_COHERENT;
			return ret;
		}
	}

	/* Check coherent device granules */
	if (arm_dev_coh.num_granules != 0UL) {
		ret = granule_addr_to_idx(addr, &arm_dev_coh);
		if (ret != UINT64_MAX) {
			*type = DEV_MEM_COHERENT;
			return ret;
		}
	}

	return UINT64_MAX;
}

static unsigned long granule_idx_to_addr(unsigned long idx,
					 struct arm_memory_layout *memory_ptr)
{
	unsigned long r, l = 0UL, addr = 0UL;

	assert(memory_ptr->num_banks != 0UL);
	assert(idx < memory_ptr->num_granules);

	r = memory_ptr->num_banks - 1UL;

	/*
	 * Calculate the start and end granule index of each bank using the
	 * start_gran_idx (which is a cumulative idx from previous memory banks)
	 * and then check whether the given index falls within it.
	 */
	while (l <= r) {
		const struct arm_memory_bank *bank;
		unsigned long i;
		unsigned long idx_start, idx_end;

		i = l + ((r - l) / 2UL);
		assert(i < PLAT_ARM_MAX_MEM_BANKS);

		bank = &memory_ptr->bank[i];

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

/* cppcheck-suppress misra-c2012-8.7 */
unsigned long plat_granule_idx_to_addr(unsigned long idx)
{
	return granule_idx_to_addr(idx, &arm_dram);
}

unsigned long plat_dev_granule_idx_to_addr(unsigned long idx, enum dev_coh_type type)
{
	(void)type;

	/* No coherent device memory */
	assert(type == DEV_MEM_NON_COHERENT);

	return granule_idx_to_addr(idx, &arm_dev_ncoh);
}


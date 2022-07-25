/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <buffer_private.h>
#include <test_harness.h>

/*
 * Get the expected VA (as per the aarch64 build) for a given slot.
 */
static inline uintptr_t slot_to_expected_va(enum buffer_slot slot)
{
	return (uintptr_t)(SLOT_VIRT + (GRANULE_SIZE * slot));
}

/*
 * Return the PA mapped to a given slot.
 *
 * NOTE:	This API assumes a 4KB granularity and that the architecture
 *		has a VA space of 48 bits.
 */
static uintptr_t slot_to_arch_pa(enum buffer_slot slot)
{
	struct xlat_table_entry *entry = get_cache_entry();
	uintptr_t va = slot_to_va(slot);
	uint64_t *desc_ptr = xlat_get_pte_from_table(entry, va);
	uint64_t descriptor = xlat_read_descriptor(desc_ptr);

	return (uintptr_t)(descriptor & XLAT_TTE_L3_PA_MASK);
}

/*
 * Helper function to find the slot VA to which a PA is mapped to.
 * This function is used to validate that the slot buffer library
 * mapped the given fake PA to the VA that would be expected by the
 * aarch64 architecture.
 */
static uintptr_t host_pa_to_slot_va(uintptr_t pa)
{
	for (unsigned int i = 0U; i < NR_CPU_SLOTS; i++) {
		if (pa == slot_to_arch_pa((enum buffer_slot)i)) {
			/*
			 * Found a slot returning the same address, get
			 * the "real" VA for that slot (the one that
			 * would be used by the aarch64 architecture).
			 */
			return slot_to_expected_va((enum buffer_slot)i);
		}
	}

	/* No buffer slot found */
	return (uintptr_t)NULL;
}

/*
 * Maps addr to the requested slot buffer and returns a pointer to the
 * fake VA for the slot (the current addr), so the host can perform R/W
 * operations on the mapped granule.
 */
void *test_buffer_map(enum buffer_slot slot,
		      unsigned long addr, bool ns)
{
	uintptr_t va = (uintptr_t)buffer_map_internal(slot, addr, ns);

	if ((void *)va == NULL) {
		return NULL;
	}

	return(void *)addr;
}

void test_buffer_unmap(void *buf)
{
	void *slot_va = (void *)host_pa_to_slot_va((uintptr_t)buf);

	assert(slot_va != NULL);

	buffer_unmap_internal(slot_va);
}

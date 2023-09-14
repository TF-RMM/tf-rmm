/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <buffer_private.h>
#include <granule.h>
#include <host_utils.h>
#include <xlat_tables.h>

/*
 * Return the PA mapped to a given slot.
 *
 * NOTE:	This API assumes a 4KB granularity and that the architecture
 *		has a VA space of 48 bits.
 */
uintptr_t realm_test_util_slot_to_pa(enum buffer_slot slot)
{
	struct xlat_llt_info *entry = get_cached_llt_info();
	uintptr_t va = slot_to_va(slot);
	uint64_t *desc_ptr = xlat_get_tte_ptr(entry, va);
	uint64_t descriptor = xlat_read_tte(desc_ptr);

	return (uintptr_t)xlat_get_oa_from_tte(descriptor);
}

/*
 * Helper function to find the slot VA to which a PA is mapped to.
 * This function is used to validate that the slot buffer library
 * mapped the given PA to the VA that would be expected by the
 * aarch64 VMSA.
 */
uintptr_t realm_test_util_slot_va_from_pa(uintptr_t pa)
{
	for (unsigned int i = 0U; i < (unsigned int)NR_CPU_SLOTS; i++) {
		if (pa == realm_test_util_slot_to_pa((enum buffer_slot)i)) {
			/*
			 * Found a slot returning the same address, get
			 * the VA for that slot (the one that would be
			 * used by the aarch64 VMSA).
			 */
			return slot_to_va((enum buffer_slot)i);
		}
	}

	/* No buffer slot found */
	return (uintptr_t)NULL;
}

/*
 * Function to return the base pointer to granule structure.
 * This function relies on addr_to_granule().
 */
struct granule *realm_test_util_granule_struct_base(void)
{
	return addr_to_granule(host_util_get_granule_base());
}

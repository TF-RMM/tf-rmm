/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <buffer_private.h>
#include <stddef.h>
#include <test_helpers.h>
#include <xlat_tables.h>

uintptr_t buffer_test_helpers_slot_to_pa(enum buffer_slot slot)
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
uintptr_t buffer_test_helpers_slot_va_from_pa(uintptr_t pa)
{
	for (unsigned int i = 0U; i < (unsigned int)NR_CPU_SLOTS; i++) {
		if (pa == buffer_test_helpers_slot_to_pa((enum buffer_slot)i)) {
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
 * Callback to mock aarch64 based slot buffer mapping to the buffer tests.
 * This function maps `addr` to the requested slot in slot buffer and returns
 * a pointer which can be read or written to by the tests on fake_host
 * architecture.
 * Note that the function maps the addr in the Stage 1 xlat tables as per
 * aarch64 VMSA and it walks the table to retrieve the PA and returns this
 * back to the caller.
 */
void *buffer_test_cb_map_access(unsigned int slot, unsigned long addr)
{
	void *va = buffer_map_internal((enum buffer_slot)slot, addr);

	if (va == NULL) {
		return NULL;
	}

	/*
	 * Perform a table walk to get the PA mapped to `slot`.
	 * If everything went well it should return the same address as `addr`.
	 */
	return (void *)buffer_test_helpers_slot_to_pa((enum buffer_slot)slot);
}

/*
 * Callback to mock aarch64 based slot buffer ummapping to the buffer tests.
 * The function receives a `buf` pointer mapped using
 * buffer_test_cb_map_access(). It needs to find the VA as per aarch64
 * VMSA based slot buffer and then it uses this va to unmap from Stage 1
 * xlat tables.
 */
void buffer_test_cb_unmap_access(void *buf)
{
	void *slot_va =
		(void *)buffer_test_helpers_slot_va_from_pa((uintptr_t)buf);

	assert(slot_va != NULL);

	buffer_unmap_internal(slot_va);
}

/*
 * Callback to map an addr to a slot as per aarch64 VMSA. Note that the address
 * to the buffer returned by this function cannot be read/written to from
 * the tests.
 */
void *buffer_test_cb_map_aarch64_vmsa(unsigned int slot, unsigned long addr)
{
	return buffer_map_internal((enum buffer_slot)slot, addr);
}

/*
 * Callback to unmap a buf mapped to a slot as per aarch64 vmsa via
 * buffer_test_cb_map_aarch64_vmsa() callback.
 */
void buffer_test_cb_unmap_aarch64_vmsa(void *buf)
{
	buffer_unmap_internal(buf);
}

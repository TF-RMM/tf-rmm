/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <realm_test_utils.h>
#include <stddef.h>

/*
 * Maps addr to the requested slot buffer and returns a pointer which can be
 * accessed for read or write by the tests. The callback maps the `addr` as
 * per aarch64 VMSA and walks the xlat tables to retrieve the original
 * `addr` thus verifying that the `addr` was mapped correctly in the tables.
 */
void *test_buffer_map_access(unsigned int slot, unsigned long addr)
{
	void *va = buffer_map_internal((enum buffer_slot)slot, addr);

	if (va == NULL) {
		return NULL;
	}

	/*
	 * Perform a table walk to get the PA mapped to `slot`.
	 * If everything went well it should return the same address as `addr`.
	 */
	return (void *)realm_test_util_slot_to_pa((enum buffer_slot)slot);
}

/*
 * Receives an accessible `buf` address corresponding to a mapped
 * slot buffer and unmaps the granule mapped to it.
 */
void test_buffer_unmap_access(void *buf)
{
	void *slot_va =
		(void *)realm_test_util_slot_va_from_pa((uintptr_t)buf);

	assert(slot_va != NULL);

	buffer_unmap_internal(slot_va);
}

/*
 * Maps addr to the requested slot buffer and returns a mapped VA
 * corresponding to the slot buffer as per aarch64 VMSA.
 */
void *test_buffer_map_aarch64_vmsa(unsigned int slot, unsigned long addr)
{
	return buffer_map_internal((enum buffer_slot)slot, addr);
}

/*
 * Receives an aarch64 VMSA `buf` address corresponding to a mapped
 * slot buffer and unmaps the granule mapped to it.
 */
void test_buffer_unmap_aarch64_vmsa(void *buf)
{
	buffer_unmap_internal(buf);
}

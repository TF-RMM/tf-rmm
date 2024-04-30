/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef BUFFER_TEST_HELPERS_H
#define BUFFER_TEST_HELPERS_H


/*
 * Return the PA mapped to a given slot.
 *
 * NOTE:	This API assumes a 4KB granularity and that the host
 *		architecture has a VA space of 48 bits.
 */
uintptr_t buffer_test_helpers_slot_to_pa(enum buffer_slot slot);

/*
 * Helper function to find the slot VA to which a PA is mapped to.
 */
uintptr_t buffer_test_helpers_slot_va_from_pa(uintptr_t pa);

/*
 * Test specific test_harness_cbs functions which are dynamically
 * overridden during test execution.
 */

void *buffer_test_cb_map_access(unsigned int slot, unsigned long addr);
void buffer_test_cb_unmap_access(void *buf);

void *buffer_test_cb_map_aarch64_vmsa(unsigned int slot, unsigned long addr);
void buffer_test_cb_unmap_aarch64_vmsa(void *buf);

#endif /* BUFFER_TEST_HELPERS_H */

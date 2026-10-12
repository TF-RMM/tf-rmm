/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */


#include <buffer.h>
#include <host_harness.h>
#include <host_utils.h>
#include <test_helpers.h>
#include <test_private.h>

static unsigned long test_fail_ns_addr;
static unsigned int test_fail_ns_map_count;
static bool test_fail_ns_map_triggered;

/* Fail the selected NS page's nth mapping attempt once. */
void host_da_test_fail_ns_map(unsigned long addr, unsigned int occurrence)
{
	test_fail_ns_addr = addr;
	test_fail_ns_map_count = occurrence;
	if (occurrence != 0U) {
		test_fail_ns_map_triggered = false;
	}
}

/* Report whether the armed NS mapping fault was consumed. */
bool host_da_test_ns_map_faulted(void)
{
	return test_fail_ns_map_triggered;
}

/*
 * Harness corresponding to CB_BUFFER_MAP.
 * This harness searches for a valid pointer to CB_BUFFER_MAP and calls it.
 * The DA fault hook can reject one NS map before the callback. With neither
 * fault nor callback, the default behavior uses mmap aliasing.
 */
void *host_buffer_arch_map(unsigned int slot, unsigned long addr)
{
	cb_buffer_map cb = (cb_buffer_map)get_cb(CB_BUFFER_MAP);

	if ((slot == (unsigned int)SLOT_NS) &&
	    (addr == test_fail_ns_addr) &&
	    (test_fail_ns_map_count > 0U)) {
		test_fail_ns_map_count--;
		if (test_fail_ns_map_count == 0U) {
			test_fail_ns_addr = 0UL;
			test_fail_ns_map_triggered = true;
			return NULL;
		}
	}

	return (cb == NULL) ? host_util_slot_map(slot, addr)
			    : cb((enum buffer_slot)slot, addr);
}

/*
 * Harness corresponding to CB_BUFFER_UNMAP.
 * This harness searches for a valid pointer to CB_BUFFER_UNMAP and calls it.
 * If there is no valid pointer, the default behavior uses mmap aliasing.
 */
void host_buffer_arch_unmap(void *buf)
{
	cb_buffer_unmap cb = (cb_buffer_unmap)get_cb(CB_BUFFER_UNMAP);

	if (cb != NULL) {
		cb(buf);
	} else {
		host_util_slot_unmap(buf);
	}
}

/* Return the host MMIO address; fake-host mappings do not distinguish PAS. */
void *host_mmio_arch_map(unsigned long addr, uint64_t pas_type)
{
	(void)pas_type;
	return (void *)addr;
}

/* Host MMIO addresses require no mapping resources to release. */
void host_mmio_arch_unmap(void *mmio)
{
	(void)mmio;
}

/*
 * Harness corresponding to CB_BUFFER_VA_TO_SLOT.
 * This harness searches for a valid pointer to CB_BUFFER_VA_TO_SLOT and calls it.
 * If there is no valid pointer, the default behavior uses mmap aliasing.
 */
unsigned int host_buffer_arch_va_to_slot(void *buf)
{
	cb_buffer_va_to_slot cb =
		(cb_buffer_va_to_slot)get_cb(CB_BUFFER_VA_TO_SLOT);

	if (cb != NULL) {
		return cb(buf);
	}

	return host_util_buf_to_slot(buf);
}


unsigned long host_gtsi_delegate(unsigned long addr)
{
	(void)addr;

	return 0;
}

unsigned long host_gtsi_undelegate(unsigned long addr)
{
	(void)addr;

	return 0;
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */


#include <buffer.h>
#include <host_harness.h>
#include <host_utils.h>
#include <test_helpers.h>
#include <test_private.h>

/*
 * Harness corresponding to CB_BUFFER_MAP.
 * This harness searches for a valid pointer to CB_BUFFER_MAP and calls it.
 * If there is no valid pointer, the default behavior uses mmap aliasing.
 */
void *host_buffer_arch_map(unsigned int slot, unsigned long addr)
{
	cb_buffer_map cb = (cb_buffer_map)get_cb(CB_BUFFER_MAP);

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

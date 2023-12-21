/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */


#include <buffer.h>
#include <host_harness.h>
#include <test_helpers.h>
#include <test_private.h>

/*
 * Harness corresponding to CB_BUFFER_MAP.
 * This harness searches for a valid pointer to CB_BUFFER_MAP and calls it.
 * If there is no valid pointer, the default behavior is to return addr
 */
void *host_buffer_arch_map(unsigned int slot, unsigned long addr)
{
	cb_buffer_map cb = (cb_buffer_map)get_cb(CB_BUFFER_MAP);

	return (cb == NULL) ? (void *)addr : cb((enum buffer_slot)slot, addr);
}

/*
 * Harness corresponding to CB_BUFFER_UNMAP.
 * This harness searches for a valid pointer to CB_BUFFER_UNMAP and calls it.
 * If there is no valid pointer, the default behavior is to do nothing.
 */
void host_buffer_arch_unmap(void *buf)
{
	cb_buffer_unmap cb = (cb_buffer_unmap)get_cb(CB_BUFFER_UNMAP);

	if (cb != NULL) {
		cb(buf);
	}
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

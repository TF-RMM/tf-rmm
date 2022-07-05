/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <host_harness.h>
#include <test_harness.h>

/*
 * Maps addr to the requested slot buffer and returns a pointer to the
 * fake VA for the slot (the current addr), so the host can perform R/W
 * operations on the mapped granule.
 */
void *host_buffer_arch_map(enum buffer_slot slot,
			   unsigned long addr, bool ns)
{
	return test_buffer_map(slot, addr, ns);
}

void host_buffer_arch_unmap(void *buf)
{
	test_buffer_unmap(buf);
}

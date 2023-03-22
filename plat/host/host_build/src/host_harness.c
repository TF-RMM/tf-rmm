/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <host_harness.h>

void *host_buffer_arch_map(unsigned int slot, unsigned long addr)
{
	(void)slot;

	return (void *)addr;
}

void host_buffer_arch_unmap(void *buf)
{
	(void)buf;
}

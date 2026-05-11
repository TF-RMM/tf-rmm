/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <buffer.h>
#include <host_harness.h>
#include <host_utils.h>

void *host_buffer_arch_map(unsigned int slot, unsigned long addr)
{
	return host_util_slot_map(slot, addr);
}

void host_buffer_arch_unmap(void *buf)
{
	host_util_slot_unmap(buf);
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

void *host_mmio_arch_map(unsigned long addr, uint64_t pas_type)
{
	(void)pas_type;
	return (void *)addr;
}

void host_mmio_arch_unmap(void *mmio)
{
	(void)mmio;
}

unsigned int host_buffer_arch_va_to_slot(void *addr)
{
	return host_util_buf_to_slot(addr);
}

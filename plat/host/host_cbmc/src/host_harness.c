/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <host_harness.h>
#include <tb_common.h>
#include <tb_granules.h>

void *host_buffer_arch_map(unsigned int slot, unsigned long addr)
{
	(void)slot;

	return (void *)addr;
}

void host_buffer_arch_unmap(void *buf)
{
	(void)buf;
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

unsigned long host_gtsi_delegate(unsigned long addr)
{
	if (get_granule_gpt(addr) == GPT_NS) {
		set_granule_gpt(addr, GPT_REALM);
		return 0UL;
	} else {
		return 1UL;
	}
}

unsigned long host_gtsi_undelegate(unsigned long addr)
{
	assert(get_granule_gpt(addr) == GPT_REALM);

	set_granule_gpt(addr, GPT_NS);
	return 0UL;
}

unsigned int host_buffer_arch_va_to_slot(void *addr)
{
	(void)addr;
	/* Return the first slot */
	return 0U;
}

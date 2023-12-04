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

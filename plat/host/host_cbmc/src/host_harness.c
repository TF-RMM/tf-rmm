/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <host_harness.h>
#include <tb_common.h>

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
	if (is_granule_gpt_ns(addr)) {
		set_granule_gpt_ns(addr, false);
		return 0UL;
	} else {
		return 1UL;
	}
}

unsigned long host_gtsi_undelegate(unsigned long addr)
{
	assert(!is_granule_gpt_ns(addr));
	set_granule_gpt_ns(addr, true);
	return 0UL;
}

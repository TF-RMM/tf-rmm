/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <host_harness.h>

unsigned long slot_vas[(unsigned int)NR_CPU_SLOTS] = { 0UL };

void *host_buffer_arch_map(unsigned int slot, unsigned long addr)
{
	assert(slot < NR_CPU_SLOTS);

	slot_vas[slot] = addr;

	return (void *)addr;
}

void host_buffer_arch_unmap(void *buf)
{
	unsigned int i;
	for (i = 0; i < (unsigned int)NR_CPU_SLOTS; i++) {
		if (slot_vas[i] == (unsigned long)buf) {
			/* The slot is cleared in the host_buffer_arch_va_to_slot function */
			return;
		}
	}
	assert(false); /* Execution should not reach this point */
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

unsigned int host_buffer_arch_va_to_slot(void *addr)
{
	unsigned int i;
	for (i = 0; i < (unsigned int)NR_CPU_SLOTS; i++) {
		if (slot_vas[i] == (unsigned long)addr) {
			slot_vas[i] = 0UL; /* Clear the slot */
			return i;
		}
	}
	assert(false); /* Execution should not reach this point */
	return i;
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <buffer.h>
#include <host_harness.h>
#include <string.h>

unsigned long slot_vas[(unsigned int)NR_CPU_SLOTS] = { 0UL };
static unsigned char slot_buffers[(unsigned int)NR_CPU_SLOTS][GRANULE_SIZE]
							__aligned(GRANULE_SIZE);

void *host_buffer_arch_map(unsigned int slot, unsigned long addr)
{
	assert(slot < NR_CPU_SLOTS);

	(void)memcpy(slot_buffers[slot], (void *)addr, GRANULE_SIZE);
	slot_vas[slot] = addr;

	return (void *)slot_buffers[slot];
}

void host_buffer_arch_unmap(void *buf)
{
	unsigned int i;

	for (i = 0; i < (unsigned int)NR_CPU_SLOTS; i++) {
		if ((void *)slot_buffers[i] == buf) {
			/* The slot is cleared in the host_buffer_arch_va_to_slot function */
			assert(slot_vas[i] != 0UL);
			(void)memcpy((void *)slot_vas[i], slot_buffers[i], GRANULE_SIZE);
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
	unsigned int i;

	for (i = 0; i < (unsigned int)NR_CPU_SLOTS; i++) {
		if ((void *)slot_buffers[i] == addr) {
			assert(slot_vas[i] != 0UL);
			slot_vas[i] = 0UL; /* Clear the slot */
			return i;
		}
	}
	assert(false); /* Execution should not reach this point */
	return i;
}

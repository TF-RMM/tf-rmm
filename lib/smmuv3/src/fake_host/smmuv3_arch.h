/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SMMUV3_ARCH_H
#define SMMUV3_ARCH_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

/*
 * Architecture-specific memory mapping for the SMMUv3 driver (fake_host).
 *
 * On the fake_host platform, physical addresses are already valid host
 * virtual addresses. This function optionally clears the memory and
 * returns the address directly.
 */
static inline uintptr_t smmuv3_arch_map(size_t size, uint64_t attr,
					uintptr_t pa, bool clear)
{
	(void)attr;

	if (pa == 0UL) {
		return 0UL;
	}

	if (clear) {
		(void)memset((void *)pa, 0, size);
	}

	return pa;
}

/*
 * Architecture-specific memory unmapping (fake_host).
 *
 * No-op on fake_host since PA == VA and memory is managed externally.
 */
static inline int smmuv3_arch_unmap(uintptr_t va, size_t size)
{
	(void)va;
	(void)size;

	return 0;
}

/*
 * Architecture-specific register write-and-ack (fake_host).
 *
 * On fake_host there is no hardware to acknowledge control register writes.
 * Simulate instant acknowledgment by writing the expected value directly
 * to the ACK register offset.
 */
static inline int smmuv3_arch_wait_for_ack(uintptr_t r_base, uint32_t ack_offset,
					   uint32_t mask, uint32_t expected)
{
	uint32_t *ack_reg = (uint32_t *)(r_base + ack_offset);

	*ack_reg = (*ack_reg & ~mask) | (expected & mask);
	return 0;
}

/*
 * Architecture-specific command queue synchronization (fake_host).
 *
 * On fake_host there is no hardware to consume commands from the queue.
 * Simulate instant command processing by advancing the consumer register
 * to match the producer register.
 */
static inline void smmuv3_arch_sync_cmdq(void *prod_reg, void *cons_reg)
{
	uint32_t prod = *(uint32_t *)prod_reg;

	*(uint32_t *)cons_reg = prod;
}

#endif /* SMMUV3_ARCH_H */

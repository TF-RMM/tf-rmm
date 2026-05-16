/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SMMUV3_ARCH_H
#define SMMUV3_ARCH_H

#include <errno.h>
#include <mmio.h>
#include <xlat_low_va.h>

/*
 * Architecture-specific memory mapping for the SMMUv3 driver.
 *
 * On aarch64, this wraps the low VA translation table mapper which sets up
 * proper page table entries for device or normal memory regions.
 */
static inline uintptr_t smmuv3_arch_map(size_t size, uint64_t attr,
					uintptr_t pa, bool clear)
{
	return xlat_low_va_map(size, attr, pa, clear);
}

/*
 * Architecture-specific memory unmapping.
 */
static inline int smmuv3_arch_unmap(uintptr_t va, size_t size)
{
	return xlat_low_va_unmap(va, size);
}

/*
 * Architecture-specific register write-and-ack.
 *
 * On real hardware, poll the ACK register until the hardware acknowledges
 * the control register write.
 */
static inline int smmuv3_arch_wait_for_ack(uintptr_t r_base, uint32_t ack_offset,
					   uint32_t mask, uint32_t expected)
{
	unsigned int retries = 0U;

	while (retries++ < 100000U) {
		uint32_t val = read32((void *)(r_base + ack_offset));

		if ((val & mask) == (expected & mask)) {
			return 0;
		}
	}

	return -ETIMEDOUT;
}

/*
 * Architecture-specific command queue synchronization.
 *
 * On real hardware, the SMMU processes commands asynchronously.
 * No action is needed; wait_cmdq_empty() polls the consumer register.
 */
static inline void smmuv3_arch_sync_cmdq(void *prod_reg, void *cons_reg)
{
	(void)prod_reg;
	(void)cons_reg;
}

#endif /* SMMUV3_ARCH_H */

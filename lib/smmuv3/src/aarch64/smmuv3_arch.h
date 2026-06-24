/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SMMUV3_ARCH_H
#define SMMUV3_ARCH_H

#include <errno.h>
#include <mmio.h>
#include <smmuv3_priv.h>
#include <string.h>
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
 * Reserve VA space at boot time for later populate/commit.
 */
static inline int smmuv3_arch_reserve(size_t size, uintptr_t *va)
{
	return xlat_low_va_reserve(size, va);
}

/*
 * Populate a previously reserved VA region with a PA mapping.
 */
static inline int smmuv3_arch_populate(uintptr_t va, uintptr_t pa,
				       size_t size, uint64_t attr)
{
	return xlat_low_va_populate(va, pa, size, attr);
}

/*
 * Commit a populated VA region, making it hardware-visible, and zero
 * the memory.
 */
static inline int smmuv3_arch_commit_clear(uintptr_t va, size_t size)
{
	int ret = xlat_low_va_commit(va, size);

	if (ret == 0) {
		(void)memset((void *)va, 0, size);
	}
	return ret;
}

/*
 * Decommit a VA region, making it hardware-invisible but keeping
 * the VA reservation and PA/attribute data.
 */
static inline int smmuv3_arch_decommit(uintptr_t va, size_t size)
{
	return xlat_low_va_decommit(va, size);
}

/*
 * Depopulate a VA region, clearing PA/attribute data and returning
 * entries to the reserved state. Must be decommitted first.
 */
static inline int smmuv3_arch_depopulate(uintptr_t va, size_t size)
{
	return xlat_low_va_depopulate(va, size);
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

	while (retries++ < MAX_RETRIES) {
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

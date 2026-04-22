/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PCPU_PVT_DATA_H
#define PCPU_PVT_DATA_H

#include <arch_helpers.h>
#include <assert.h>
#include <mapped_va_arch.h>
#include <pcpu_data.h>
#include <stdbool.h>

/*
 * Per-CPU runtime data stored in each CPU's private-data area.
 */
struct pcpu_pvt_data {
	/* Whether the current CPU's SIMD live state is saved in memory. */
	bool simd_state_saved;
} __aligned(GRANULE_SIZE);

COMPILER_ASSERT(sizeof(struct pcpu_pvt_data) ==
		(PCPU_PVT_DATA_PAGES * GRANULE_SIZE));

static inline struct pcpu_pvt_data *my_pcpu_pvt_data(void)
{
	assert(is_mmu_enabled());
	/*
	 * TPIDR_EL2 always stores the current CPU's metadata base together with
	 * the CPU ID encoded in the low GRANULE_SHIFT bits. On AArch64, accesses
	 * after pcpu_switch_to_high_va() should use the fixed high VA. On
	 * fake_host, accesses must continue using the backing PA because the host
	 * does not perform address translation.
	 */
	return (struct pcpu_pvt_data *)MAPPED_VA_ARCH(
			PCPU_PVT_DATA_BASE_VA,
			(read_tpidr_el2() & GRANULE_MASK) +
			(PCPU_METADATA_PAGES * GRANULE_SIZE));
}

static inline bool pcpu_pvt_simd_state_is_saved(void)
{
	return my_pcpu_pvt_data()->simd_state_saved;
}

static inline void pcpu_pvt_simd_state_set_saved(bool saved)
{
	my_pcpu_pvt_data()->simd_state_saved = saved;
}

#endif /* PCPU_PVT_DATA_H */

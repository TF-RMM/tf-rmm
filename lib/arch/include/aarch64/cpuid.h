/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef CPUID_H
#define CPUID_H

#include <arch_helpers.h>
#include <assert.h>
#include <utils_def.h>

static inline unsigned int my_cpuid(void)
{
	unsigned int cpuid;

	/*
	 * TPIDR_EL2 stores the CPU ID in the low GRANULE_SHIFT bits.
	 * The upper bits store either the PA or VA of the per-CPU metadata,
	 * depending on how far through the boot process of the current CPU we reached.
	 * See cpu_metadata_early_init() and pcpu_switch_to_high_va().
	 */
	cpuid = (unsigned int)(read_tpidr_el2() & (GRANULE_SIZE - 1UL));

	assert(cpuid < MAX_CPUS);
	return cpuid;
}

#endif /* CPUID_H */

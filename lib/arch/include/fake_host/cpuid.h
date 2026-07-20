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
	 * The upper bits store the address to the per-CPU metadata. This is
	 * the address of the `fake_host_pcpu_regions[cpu_index]` array.
	 */
	cpuid = (unsigned int)(read_tpidr_el2() & (GRANULE_SIZE - 1UL));

	assert(cpuid < MAX_CPUS);
	return cpuid;
}

#endif /* CPUID_H */

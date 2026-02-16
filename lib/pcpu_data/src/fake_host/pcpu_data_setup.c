/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <pcpu_data.h>
#include <stdint.h>

/*
 * Fake-host builds do not enter through the EL2 assembly boot path, so they
 * need a small C bootstrap that creates one per-CPU region per CPU and
 * programs TPIDR_EL2 the same way the real entry path would.
 */
static unsigned char fake_host_pcpu_regions[MAX_CPUS]
		[PCPU_REGION_PAGES * GRANULE_SIZE]
		__aligned(GRANULE_SIZE);

void pcpu_fake_host_setup(unsigned long cpu_index, uint64_t token)
{
	uintptr_t region_base;

	assert(cpu_index < MAX_CPUS);

	if (token != 0UL) {
		region_base = token;
	} else {
		region_base = (uintptr_t)fake_host_pcpu_regions[cpu_index];
	}

	pcpu_metadata_early_init(region_base, cpu_index, token);
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <smmuv3.h>
#include <stdbool.h>
#include <stdint.h>

/* Dummy SMMUv3 library functions */

int smmuv3_inv(void)
{
	return 0;
}

int smmuv3_inv_entries(unsigned long smmu_idx, unsigned int vmid)
{
	(void)smmu_idx;
	(void)vmid;

	return 0;
}

int smmuv3_inv_at_level(unsigned int vmid, unsigned long addr, long level,
			unsigned long num_entrs, bool leaf)
{
	(void)vmid;
	(void)addr;
	(void)level;
	(void)num_entrs;
	(void)leaf;

	return 0;
}

int smmuv3_inv_at_level_per_vmids(unsigned int *vmid_list, unsigned int nvmids,
				  unsigned long addr, long level,
				  unsigned long num_entrs, bool leaf)
{
	(void)vmid_list;
	(void)nvmids;
	(void)addr;
	(void)level;
	(void)num_entrs;
	(void)leaf;

	return 0;
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <smmuv3.h>

/* Dummy SMMUv3 library functions */

int smmuv3_inv(void)
{
	return 0;
}

int smmuv3_inv_page(unsigned int vmid, unsigned long addr)
{
	(void)vmid;
	(void)addr;

	return 0;
}

int smmuv3_inv_block(unsigned int vmid, unsigned long addr)
{
	(void)vmid;
	(void)addr;

	return 0;
}

int smmuv3_inv_pages_in_block(unsigned int vmid, unsigned long addr)
{
	(void)vmid;
	(void)addr;

	return 0;
}

int smmuv3_inv_entries(unsigned long smmu_idx, unsigned int vmid)
{
	(void)smmu_idx;
	(void)vmid;

	return 0;
}

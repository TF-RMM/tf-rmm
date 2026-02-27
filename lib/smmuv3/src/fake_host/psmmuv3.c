/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <psmmuv3.h>
#include <stddef.h>

struct smmuv3_dev;
struct psmmu_params;

struct smmuv3_dev *psmmu_find(unsigned long psmmu_ptr)
{
	(void)psmmu_ptr;

	return NULL;
}

bool psmmu_validate_params(struct smmuv3_dev *smmu, struct psmmu_params *params)
{
	(void)smmu;
	(void)params;

	return true;
}

bool psmmu_validate_sid(struct smmuv3_dev *smmu, unsigned long sid)
{
	(void)smmu;
	(void)sid;

	return true;
}

int psmmu_activate(struct smmuv3_dev *smmu)
{
	(void)smmu;

	return 0;
}

int psmmu_deactivate(struct smmuv3_dev *smmu)
{
	(void)smmu;

	return 0;
}

int psmmu_allocate_st_l2(struct smmuv3_dev *smmu, unsigned long sid)
{
	(void)smmu;
	(void)sid;

	return 0;
}

int psmmu_release_st_l2(struct smmuv3_dev *smmu, unsigned long sid)
{
	(void)smmu;
	(void)sid;

	return 0;
}


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

int psmmu_release_st_l2(struct smmuv3_dev *smmu, unsigned long sid,
		       uintptr_t *l2tab_pa)
{
	(void)smmu;
	(void)sid;
	(void)l2tab_pa;

	return 0;
}

size_t psmmu_strtab_size(struct smmuv3_dev *smmu)
{
	(void)smmu;

	return 0UL;
}

int psmmu_register_st_l1(struct smmuv3_dev *smmu, uintptr_t l1_st_pa,
			 uintptr_t l2_ds_pa)
{
	(void)smmu;
	(void)l1_st_pa;
	(void)l2_ds_pa;

	return 0;
}

int psmmu_register_queues(struct smmuv3_dev *smmu, uintptr_t cmdq_pa,
			  uintptr_t evtq_pa)
{
	(void)smmu;
	(void)cmdq_pa;
	(void)evtq_pa;

	return 0;
}

int psmmu_register_st_l2(struct smmuv3_dev *smmu, unsigned long sid, uintptr_t l2tab_pa)
{
	(void)smmu;
	(void)sid;
	(void)l2tab_pa;

	return 0;
}

void psmmu_get_donated(struct smmuv3_dev *smmu, uintptr_t *range_base,
		       unsigned long *range_size)
{
	(void)smmu;
	(void)range_base;
	(void)range_size;
}

bool psmmu_set_busy(struct smmuv3_dev *smmu, unsigned int state)
{
	(void)smmu;
	(void)state;

	return true;
}

void psmmu_set_active(struct smmuv3_dev *smmu)
{
	(void)smmu;
}

void psmmu_set_inactive(struct smmuv3_dev *smmu)
{
	(void)smmu;
}

void psmmu_unmap(struct smmuv3_dev *smmu)
{
	(void)smmu;
}


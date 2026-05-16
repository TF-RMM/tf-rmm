/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#ifndef SMMUV3_PSMMU_H
#define SMMUV3_PSMMU_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/*
 * Indices into psmmu_range[] identifying the different memory ranges
 * donated by the host during RMI_PSMMU_ACTIVATE.
 */
/* cppcheck-suppress misra-c2012-2.4 */
enum psmmu_l1_mem_range {
	/* L1 Stream Table */
	PSMMU_MEM_RANGE_L1_ST = 0U,
	/* l2strtab[] array (one entry per L1STD, same size as L1 table) */
	PSMMU_MEM_RANGE_L2_DS,
	/* SMMUv3 Command queue */
	PSMMU_MEM_RANGE_CMDQ,
	/* SMMUv3 Event queue */
	PSMMU_MEM_RANGE_EVTQ,
	/* Total number of memory ranges */
	PSMMU_MEM_RANGE_NUM
};

struct smmuv3_dev;
struct psmmu_params;

struct smmuv3_dev *smmuv3_psmmu_find(unsigned long psmmu_ptr);
bool smmuv3_psmmu_validate_params(struct smmuv3_dev *smmu, struct psmmu_params *params);
bool smmuv3_psmmu_validate_sid(struct smmuv3_dev *smmu, unsigned long sid);
bool smmuv3_psmmu_set_busy(struct smmuv3_dev *smmu, unsigned int state);
void smmuv3_psmmu_set_active(struct smmuv3_dev *smmu);
void smmuv3_psmmu_set_inactive(struct smmuv3_dev *smmu);

/*
 * These functions are called during RMI_PSMMU_ACTIVATE while
 * in the PSMMU_BUSY state. They do not acquire or release the lock.
 */
size_t smmuv3_psmmu_strtab_size(struct smmuv3_dev *smmu);
int smmuv3_psmmu_register_st_l1(struct smmuv3_dev *smmu, uintptr_t l1_st_pa,
				uintptr_t l2_ds_pa);
int smmuv3_psmmu_register_queues(struct smmuv3_dev *smmu, uintptr_t cmdq_pa,
				 uintptr_t evtq_pa);
int smmuv3_psmmu_activate(struct smmuv3_dev *smmu);

/*
 * These functions are called during RMI_PSMMU_DEACTIVATE while
 * in the PSMMU_BUSY state. They do not acquire or release the lock.
 */
int smmuv3_psmmu_deactivate(struct smmuv3_dev *smmu);
void smmuv3_psmmu_get_donated(struct smmuv3_dev *smmu, uintptr_t *range_base,
				unsigned long *range_size);

/*
 * Called during RMI_PSMMU_DEACTIVATE and RMI_PSMMU_ACTIVATE
 * if an error occurs.
 */
void smmuv3_psmmu_unmap(struct smmuv3_dev *smmu);

/*
 * These functions are called during RMI_PSMMU_ST_L2_CREATE
 * and RMI_PSMMU_ST_L2_DESTROY.
 */
int smmuv3_psmmu_register_st_l2(struct smmuv3_dev *smmu, unsigned long sid,
				uintptr_t l2tab_pa);
int smmuv3_psmmu_release_st_l2(struct smmuv3_dev *smmu, unsigned long sid,
				uintptr_t *l2tab_pa);

/*
 * Reset the PSMMU to post-init state (PSMMU_INACTIVE).
 * Intended for unit test teardown.
 */
void smmuv3_psmmu_reset(struct smmuv3_dev *smmu);

#endif /* SMMUV3_PSMMU_H */

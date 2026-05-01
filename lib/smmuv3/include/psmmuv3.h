/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#ifndef PSMMUV3_H
#define PSMMUV3_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

struct smmuv3_dev;
struct psmmu_params;

struct smmuv3_dev *psmmu_find(unsigned long psmmu_ptr);
bool psmmu_validate_params(struct smmuv3_dev *smmu, struct psmmu_params *params);
bool psmmu_validate_sid(struct smmuv3_dev *smmu, unsigned long sid);
bool psmmu_set_busy(struct smmuv3_dev *smmu, unsigned int state);
void psmmu_set_inactive(struct smmuv3_dev *smmu);

/*
 * These functions are called during RMI_PSMMU_ACTIVATE while
 * in the PSMMU_BUSY state. They do not acquire or release the lock.
 */
size_t psmmu_strtab_size(struct smmuv3_dev *smmu);
int psmmu_register_st_l1(struct smmuv3_dev *smmu, uintptr_t *donated_pa);
int psmmu_register_queues(struct smmuv3_dev *smmu);
int psmmu_activate(struct smmuv3_dev *smmu);

/*
 * These functions are called during RMI_PSMMU_DEACTIVATE while
 * in the PSMMU_BUSY state. They do not acquire or release the lock.
 */
int psmmu_deactivate(struct smmuv3_dev *smmu);
unsigned long psmmu_get_donated(struct smmuv3_dev *smmu, uintptr_t *donated_pa);

/*
 * These functions are called during RMI_PSMMU_ST_L2_CREATE
 * and RMI_PSMMU_ST_L2_DESTROY.
 */
int psmmu_validate_st_l2(struct smmuv3_dev *smmu, unsigned long sid, uintptr_t *l2tab_pa);
int psmmu_register_st_l2(struct smmuv3_dev *smmu, unsigned long sid, uintptr_t l2tab_pa);
int psmmu_release_st_l2(struct smmuv3_dev *smmu, unsigned long sid);

#endif /* PSMMUV3_H */

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#ifndef PSMMUV3_H
#define PSMMUV3_H

#include <stdbool.h>
#include <stdint.h>

struct smmuv3_dev;
struct psmmu_params;

struct smmuv3_dev *psmmu_find(unsigned long psmmu_ptr);
bool psmmu_validate_params(struct smmuv3_dev *smmu, struct psmmu_params *params);
bool psmmu_validate_sid(struct smmuv3_dev *smmu, unsigned long sid);
int psmmu_activate(struct smmuv3_dev *smmu);
int psmmu_deactivate(struct smmuv3_dev *smmu);
int psmmu_allocate_st_l2(struct smmuv3_dev *smmu, unsigned long sid);
int psmmu_release_st_l2(struct smmuv3_dev *smmu, unsigned long sid);

#endif /* PSMMUV3_H */

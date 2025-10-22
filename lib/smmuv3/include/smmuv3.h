/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#ifndef SMMUV3_H
#define SMMUV3_H

#include <rmm_el3_ifc.h>

void setup_smmuv3_layout(struct smmu_list *plat_smmu_list);

int smmuv3_init(void);

#endif /* SMMUV3_H */

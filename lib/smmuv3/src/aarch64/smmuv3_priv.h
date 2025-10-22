/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#ifndef SMMUV3_PRIV_H
#define SMMUV3_PRIV_H

struct smmu_info;

struct arm_smmu_layout {
	/* Number of SMMUv3 */
	uint64_t num_smmus;
	/* Array of SMMUv3 Info structures */
	struct smmu_info arm_smmu_info[RMM_MAX_SMMUS];
};

#endif /* SMMUV3_PRIV_H */

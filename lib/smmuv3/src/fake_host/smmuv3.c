/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <smmuv3.h>

/* Dummy SMMUv3 library functions */

int smmuv3_init(void)
{
	return 0;
}

int smmuv3_configure_stream(unsigned long smmu_idx,
			    struct smmu_stg2_config *s2_cfg,
			    unsigned int sid)
{
	(void)smmu_idx;
	(void)s2_cfg;
	(void)sid;

	return 0;
}

int smmuv3_enable_ste(unsigned long smmu_idx, unsigned int sid)
{
	(void)smmu_idx;
	(void)sid;

	return 0;
}

int smmuv3_disable_ste(unsigned long smmu_idx, unsigned int sid)
{
	(void)smmu_idx;
	(void)sid;

	return 0;
}

int smmuv3_allocate_ste(unsigned long smmu_idx, unsigned int sid)
{
	(void)smmu_idx;
	(void)sid;

	return 0;
}

int smmuv3_release_ste(unsigned long smmu_idx, unsigned int sid)
{
	(void)smmu_idx;
	(void)sid;

	return 0;
}

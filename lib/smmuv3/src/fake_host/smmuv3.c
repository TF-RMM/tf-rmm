/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <smmuv3.h>

/* Dummy SMMUv3 library functions */

int smmuv3_init(uintptr_t driv_hdl, size_t hdl_sz)
{
	(void)driv_hdl;
	(void)hdl_sz;
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

uintptr_t smmuv3_driver_setup(struct smmu_list *plat_smmu_list, uintptr_t *out_pa,
				size_t *out_sz)
{
	(void)plat_smmu_list;
	(void)out_pa;
	(void)out_sz;

	return 1UL;
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <stdbool.h>
#include <tb_common.h>

unsigned int rmm_el3_ifc_get_manifest_version(void)
{
	ASSERT(false, "rmm_el3_ifc_get_manifest_version");
	return 0U;
}

int rmm_el3_ifc_bdf_to_smmu(unsigned long ecam_addr, unsigned int bdf,
			    unsigned int *smmu_idx, unsigned int *sid)
{
	ASSERT(false, "rmm_el3_ifc_bdf_to_smmu");
	return 0;
}
#endif /* CBMC */

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

bool rmm_el3_ifc_is_ecam_base_valid(unsigned long ecam_addr)
{
	(void)ecam_addr;
	return true;
}

bool rmm_el3_ifc_is_bdf_valid(unsigned long ecam_addr, unsigned int bdf)
{
	(void)ecam_addr;
	(void)bdf;
	return true;
}

bool rmm_el3_ifc_is_root_port_id_valid(unsigned long ecam_addr,
				       unsigned int root_port_id)
{
	(void)ecam_addr;
	(void)root_port_id;
	return true;
}
#endif /* CBMC */

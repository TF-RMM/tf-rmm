/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <assert.h>
#include <rmm_el3_ifc.h>
#include <smmuv3.h>
#include <smmuv3_priv.h>

static struct arm_smmu_layout arm_smmu;

/* cppcheck-suppress misra-c2012-8.7 */
void setup_smmuv3_layout(struct smmu_list *plat_smmu_list)
{
	struct smmu_info *smmus_ptr;

	assert(plat_smmu_list != NULL);

	arm_smmu.num_smmus = plat_smmu_list->num_smmus;
	smmus_ptr = plat_smmu_list->smmus;

	for (uint64_t i = 0UL; i < plat_smmu_list->num_smmus; i++) {
		arm_smmu.arm_smmu_info[i] = *smmus_ptr++;
	}
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arm_root_complex.h>
#include <assert.h>
#include <utils_def.h>

/* PCIe Root Complex info structure version */
static uint32_t gbl_arm_rc_info_version;

/* Number of valid PCIe Root Complex info structures, initialized during boot */
static uint32_t gbl_arm_rc_info_count;

static struct arm_root_complex_info gbl_arm_rc_info[PLAT_ARM_ROOT_COMPLEX_MAX];

static void arm_set_root_port_info(struct arm_root_port_info *arm_rp_info,
				   struct root_port_info *rp_info)
{
	assert(rp_info->num_bdf_mappings <= PLAT_ARM_BDF_MAPPINGS_MAX);

	arm_rp_info->root_port_id = rp_info->root_port_id;

	/* setup BDF mappings */
	for (uint32_t i = 0U; i < rp_info->num_bdf_mappings; i++) {
		struct arm_bdf_mapping_info *arm_bdf_info;
		struct bdf_mapping_info *bdf_info;

		arm_bdf_info = &arm_rp_info->arm_bdf_info[i];
		bdf_info = &rp_info->bdf_mappings[i];

		arm_bdf_info->mapping_base = bdf_info->mapping_base;
		arm_bdf_info->mapping_top  = bdf_info->mapping_top;
		arm_bdf_info->mapping_off = bdf_info->mapping_off;
		arm_bdf_info->smmu_idx = bdf_info->smmu_idx;
	}
}

static void arm_set_root_complex_info(struct arm_root_complex_info *arm_rc_info,
				      struct root_complex_info *rc_info)
{
	uint32_t rp_idx;

	assert(rc_info->num_root_ports <= PLAT_ARM_ROOT_PORT_MAX);

	arm_rc_info->ecam_base = rc_info->ecam_base;
	arm_rc_info->segment = rc_info->segment;

	for (rp_idx = 0U; rp_idx < rc_info->num_root_ports; rp_idx++) {
		arm_set_root_port_info(&arm_rc_info->arm_rp_info[rp_idx],
				       &rc_info->root_ports[rp_idx]);
	}
}

/* Setup Arm platform Root Complex details from details from Boot manifest */
void arm_set_root_complex_list(struct root_complex_list *rc_list)
{
	uint32_t rc_idx;

	assert(rc_list != NULL);
	assert(rc_list->num_root_complex <= PLAT_ARM_ROOT_COMPLEX_MAX);

	gbl_arm_rc_info_version = rc_list->rc_info_version;
	gbl_arm_rc_info_count = (uint32_t)rc_list->num_root_complex;

	for (rc_idx = 0U; rc_idx < rc_list->num_root_complex; rc_idx++) {
		arm_set_root_complex_info(&gbl_arm_rc_info[rc_idx],
					  &rc_list->root_complex[rc_idx]);
	}
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <buffer.h>
#include <debug.h>
#include <feature.h>
#include <psmmu.h>
#include <psmmuv3.h>

/*
 * Activate a PSMMU.
 *
 * Parameters:
 *   psmmu_ptr	- Physical address of PSMMU identified by the base physical address of
 *		  SMMUv3_PAGE_0 for the Non-secure SMMU instance.
 *   params_ptr	- Physical address of PSMMU parameters.
 *
 * Return:
 *		- Command result.
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long smc_psmmu_activate(unsigned long psmmu_ptr,
				 unsigned long params_ptr)
{
	struct granule *g_smmu_params;
	struct psmmu_params params;
	struct smmuv3_dev *smmu;

	if (!is_rmi_feat_da_enabled()) {
		return RMI_ERROR_NOT_SUPPORTED;
	}

	smmu = psmmu_find(psmmu_ptr);
	if (smmu == NULL) {
		return RMI_ERROR_INPUT;
	}

	g_smmu_params = find_granule(params_ptr);
	if ((g_smmu_params == NULL) ||
		(granule_unlocked_state(g_smmu_params) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	if (!ns_buffer_read(SLOT_NS, g_smmu_params, 0U,
				sizeof(struct psmmu_params), &params)) {
		return RMI_ERROR_INPUT;
	}

	/* Validate PSMMU parameters */
	/* coverity[uninit_use_in_call:SUPPRESS] */
	if (!psmmu_validate_params(smmu, &params)) {
		return RMI_ERROR_INPUT;
	}

	if (psmmu_activate(smmu) != 0) {
		return RMI_ERROR_INPUT;
	}

	return RMI_SUCCESS;
}

/*
 * Deactivate a PSMMU.
 *
 * Parameters:
 *   psmmu_ptr	- Physical address of PSMMU identified by the base physical address of
 *		  SMMUv3_PAGE_0 for the Non-secure SMMU instance.
 *
 * Return:
 *		- Command result.
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long smc_psmmu_deactivate(unsigned long psmmu_ptr)
{
	struct smmuv3_dev *smmu;

	if (!is_rmi_feat_da_enabled()) {
		return RMI_ERROR_NOT_SUPPORTED;
	}

	smmu = psmmu_find(psmmu_ptr);
	if (smmu == NULL) {
		return RMI_ERROR_INPUT;
	}

	if (psmmu_deactivate(smmu) != 0) {
		return RMI_ERROR_INPUT;
	}

	return RMI_SUCCESS;
}

/*
 * Create a PSMMU Level 2 Stream Table.
 *
 * Parameters:
 *   psmmu_ptr	- Physical address of PSMMU identified by the base physical address of
 *		  SMMUv3_PAGE_0 for the Non-secure SMMU instance.
 *   sid	- Base of StreamID range described by the Level 2 Stream Table.
 *
 * Return:
 *		- Command result.
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long smc_psmmu_st_l2_create(unsigned long psmmu_ptr, unsigned long sid)
{
	struct smmuv3_dev *smmu;

	if (!is_rmi_feat_da_enabled()) {
		return RMI_ERROR_NOT_SUPPORTED;
	}

	smmu = psmmu_find(psmmu_ptr);
	if (smmu == NULL) {
		return RMI_ERROR_INPUT;
	}

	if (!psmmu_validate_sid(smmu, sid)) {
		return RMI_ERROR_INPUT;
	}

	if (psmmu_allocate_st_l2(smmu, sid) != 0) {
		return RMI_ERROR_INPUT;
	}

	return RMI_SUCCESS;
}
/*
 * Destroy a PSMMU Level 2 Stream Table.
 *
 * Parameters:
 *   psmmu_ptr	- Physical address of PSMMU identified by the base physical address of
 *		  SMMUv3_PAGE_0 for the Non-secure SMMU instance.
 *   sid	- Base of StreamID range described by the Level 2 Stream Table.
 *
 * Return:
 *		- Command result.
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long smc_psmmu_st_l2_destroy(unsigned long psmmu_ptr, unsigned long sid)
{
	struct smmuv3_dev *smmu;

	if (!is_rmi_feat_da_enabled()) {
		return RMI_ERROR_NOT_SUPPORTED;
	}

	smmu = psmmu_find(psmmu_ptr);
	if (smmu == NULL) {
		return RMI_ERROR_INPUT;
	}

	if (!psmmu_validate_sid(smmu, sid)) {
		return RMI_ERROR_INPUT;
	}

	if (psmmu_release_st_l2(smmu, sid) != 0) {
		return RMI_ERROR_INPUT;
	}

	return RMI_SUCCESS;
}

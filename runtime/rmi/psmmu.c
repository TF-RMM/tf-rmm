/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <buffer.h>
#include <debug.h>
#include <feature.h>
#include <psmmu.h>
#include <smmuv3_psmmu.h>
#include <sro_context.h>
#include <sro_smmu.h>
#include <xlat_defs.h>

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
void smc_psmmu_activate(unsigned long psmmu_ptr, unsigned long params_ptr,
			struct smc_result *res)
{
	struct granule *g_smmu_params;
	struct psmmu_params params;
	struct smmuv3_dev *smmu;
	struct sro_context *sro;
	unsigned long cmdq_grans, evtq_grans, l1st_grans;
	unsigned long ret;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = RMI_ERROR_NOT_SUPPORTED;
		return;
	}

	smmu = smmuv3_psmmu_find(psmmu_ptr);
	if (smmu == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	g_smmu_params = find_granule(params_ptr);
	if ((g_smmu_params == NULL) ||
		(granule_unlocked_state(g_smmu_params) != GRANULE_STATE_NS)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!ns_buffer_read(SLOT_NS, g_smmu_params, 0U,
				sizeof(struct psmmu_params), &params)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/* Validate PSMMU parameters */
	/* coverity[uninit_use_in_call:SUPPRESS] */
	if (!smmuv3_psmmu_validate_params(smmu, &params)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!smmuv3_psmmu_set_busy(smmu, PSMMU_INACTIVE)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * Calculate the number of granules required for CMDQ, EVTQ
	 * and the L1 Stream Table.
	 */
	cmdq_grans = smmuv3_psmmu_cmdq_alloc_size(smmu) / GRANULE_SIZE;
	evtq_grans = smmuv3_psmmu_evtq_alloc_size(smmu) / GRANULE_SIZE;
	l1st_grans = smmuv3_psmmu_strtab_size(smmu) / GRANULE_SIZE;

	/*
	 * Reserve an SRO context handle.
	 * The operaton cannot be cancelled.
	 * The requested memory is contiguous.
	 */
	ret = sro_ctx_reserve(SMC_RMI_PSMMU_ACTIVATE,
				l1st_grans * GRANULE_SIZE,
				false, true,
				SMC_RMI_OP_MEM_DONATE);
	if (ret != RMI_SUCCESS) {
		smmuv3_psmmu_set_inactive(smmu);
		res->x[0] = ret;
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);

	sro->smmu_ctx.smmu_ptr = smmu;
	sro->smmu_ctx.sid = UL(-1);

	/* Prepare memory donation ranges */

	/* L1 Stream Table */
	sro->smmu_ctx.smmu_range[(unsigned int)PSMMU_MEM_RANGE_L1_ST].requested = l1st_grans;
	sro->smmu_ctx.smmu_range[(unsigned int)PSMMU_MEM_RANGE_L1_ST].contig =
									RMI_OP_MEM_CONTIG;
	/* Command queue */
	sro->smmu_ctx.smmu_range[(unsigned int)PSMMU_MEM_RANGE_CMDQ].requested = cmdq_grans;
	sro->smmu_ctx.smmu_range[(unsigned int)PSMMU_MEM_RANGE_CMDQ].contig =
									RMI_OP_MEM_CONTIG;
	/* Event queue */
	sro->smmu_ctx.smmu_range[(unsigned int)PSMMU_MEM_RANGE_EVTQ].requested = evtq_grans;
	sro->smmu_ctx.smmu_range[(unsigned int)PSMMU_MEM_RANGE_EVTQ].contig =
									RMI_OP_MEM_CONTIG;
	smmu_prepare_donate(sro, SRO_ACTIVATE_START, res);
}

/**************************************************************************
 * Set of handler callbacks for RMI_PSMMU_ACTIVATE.
 *
 * The following set of functions implement a state machine for
 * RMI_PSMMU_ACTIVATE and SRO support.
 **************************************************************************/
/*
 * SRO handle callback for RMI_OP_MEM_DONATE during RMI_PSMMU_ACTIVATE.
 */
void psmmu_activate_start(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	struct sro_context *sro = my_sro_ctx();
	unsigned int range_idx;
	int ret;

	/* Validate that this was invoked from RMI_OP_MEM_DONATE */
	assert(fid == SMC_RMI_OP_MEM_DONATE);
	assert(sro != NULL);

	ret = smmu_memory_donate(sro, res);
	if (ret == 0) {
		/* Empty donation; request more memory from the host */
		return;
	}

	if (ret < 0) {
		/*
		 * The command failed, so request the host to reclaim
		 * the donated memory and return.
		 */
		smmu_prepare_reclaim(sro, SRO_RECLAIM_START, RMI_ERROR_INPUT, false, res);
		return;
	}

	/* Index of the range to donate */
	range_idx = sro->smmu_ctx.range_idx;

	if (++range_idx < (unsigned int)PSMMU_MEM_RANGE_NUM) {
		/* Next memory range */
		unsigned long requested = sro->smmu_ctx.smmu_range[range_idx].requested;
		unsigned long contig = sro->smmu_ctx.smmu_range[range_idx].contig;

		sro->smmu_ctx.range_idx = range_idx;

		/* Initialize the SRO context for the next interation */
		sro->smmu_ctx.requested = requested;
		sro->smmu_ctx.transferred = 0UL;

		/* RmiResult with RmiResultDataIncomplete */
		res->x[0] = (RMI_INCOMPLETE |
				INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_DONATE) |
				INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL));

		/* RmiOpMemDonateReq */
		res->x[2] = rmi_op_donate_req_encode(
					requested * GRANULE_SIZE,
					contig,
					RMI_OP_MEM_DELEGATED);
		return;
	}

	/* Setup the callback for the next stage */
	sro->smmu_ctx.cb_id = (unsigned int)SRO_ACTIVATE_FINISH;

	/* RmiResult with RmiResultDataIncomplete */
	res->x[0] = (RMI_INCOMPLETE |
		     INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_NONE) |
		     INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL));
	res->x[2] = 0UL;
}

/*
 * SRO handle callback for SMC_RMI_OP_CONTINUE during RMI_PSMMU_ACTIVATE.
 */
void psmmu_activate_finish(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	struct sro_context *sro = my_sro_ctx();
	struct smmuv3_dev *smmu;
	int ret;

	/* Validate that this was invoked from RMI_OP_CONTINUE */
	assert(fid == SMC_RMI_OP_CONTINUE);
	assert(sro != NULL);

	smmu = sro->smmu_ctx.smmu_ptr;
	assert(smmu != NULL);

	res->x[2] = 0UL;

	ret = smmuv3_psmmu_register_st_l1(smmu,
			sro->smmu_ctx.smmu_range[(unsigned int)PSMMU_MEM_RANGE_L1_ST].base);
	if (ret != 0) {
		goto unmap_reclaim;
	}

	ret = smmuv3_psmmu_register_queues(smmu,
			sro->smmu_ctx.smmu_range[(unsigned int)PSMMU_MEM_RANGE_CMDQ].base,
			sro->smmu_ctx.smmu_range[(unsigned int)PSMMU_MEM_RANGE_EVTQ].base);
	if (ret != 0) {
		goto unmap_reclaim;
	}

	/*
	 * Initialize and enable the SMMUv3 device.
	 * Set state to PSMMU_ACTIVE.
	 */
	ret = smmuv3_psmmu_activate(smmu);
	if (ret == 0) {
		res->x[0] = RMI_SUCCESS;
		return;
	}

unmap_reclaim:
	smmuv3_psmmu_unmap(smmu);
	smmu_prepare_reclaim(sro, SRO_RECLAIM_START, RMI_ERROR_INPUT, false, res);
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
void smc_psmmu_deactivate(unsigned long psmmu_ptr, struct smc_result *res)
{
	struct smmuv3_dev *smmu;
	struct sro_context *sro;
	uintptr_t bases[SRO_SMMU_RANGES];
	unsigned long sizes[SRO_SMMU_RANGES];
	unsigned long total = 0UL;
	unsigned long ret;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = RMI_ERROR_NOT_SUPPORTED;
		return;
	}

	smmu = smmuv3_psmmu_find(psmmu_ptr);
	if (smmu == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!smmuv3_psmmu_set_busy(smmu, PSMMU_ACTIVE)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * Reserve an SRO context handle.
	 * The operaton cannot be cancelled.
	 */
	ret = sro_ctx_reserve(SMC_RMI_PSMMU_DEACTIVATE, 0UL,
			      false, true, SMC_RMI_OP_MEM_RECLAIM);
	if (ret != RMI_SUCCESS) {
		smmuv3_psmmu_set_active(smmu);
		res->x[0] = ret;
		return;
	}

	if (smmuv3_psmmu_deactivate(smmu) != 0) {
		smmuv3_psmmu_set_active(smmu);
		sro_ctx_release();
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);

	sro->smmu_ctx.smmu_ptr = smmu;
	sro->smmu_ctx.sid = UL(-1);

	/*
	 * Retrieve the base PA and size of each donated range from the
	 * driver. memory_reclaim() will reconstruct individual granule
	 * PAs from these ranges.
	 */
	smmuv3_psmmu_get_donated(smmu, bases, sizes);

	for (unsigned int i = 0U; i < (unsigned int)PSMMU_MEM_RANGE_NUM; i++) {
		sro->smmu_ctx.smmu_range[i].base = bases[i];
		sro->smmu_ctx.smmu_range[i].requested = sizes[i];
		total += sizes[i];
	}

	/* Set contig flags for reclaim path */
	sro->smmu_ctx.smmu_range[(unsigned int)PSMMU_MEM_RANGE_L1_ST].contig =
								RMI_OP_MEM_CONTIG;
	sro->smmu_ctx.smmu_range[(unsigned int)PSMMU_MEM_RANGE_CMDQ].contig =
								RMI_OP_MEM_CONTIG;
	sro->smmu_ctx.smmu_range[(unsigned int)PSMMU_MEM_RANGE_EVTQ].contig =
								RMI_OP_MEM_CONTIG;

	sro->smmu_ctx.total_transferred = total;
	sro->smmu_ctx.range_idx = (unsigned int)PSMMU_MEM_RANGE_NUM - 1U;

	smmu_prepare_reclaim(sro, SRO_DEACTIVATE_START, RMI_SUCCESS, true, res);
}

/**************************************************************************
 * Set of handler callbacks for RMI_PSMMU_DEACTIVATE.
 *
 * The following set of functions implement a state machine for
 * RMI_PSMMU_DEACTIVATE and SRO support.
 **************************************************************************/
/*
 * SRO handle callback for SMC_RMI_OP_MEM_RECLAIM during RMI_PSMMU_DEACTIVATE.
 */
void psmmu_deactivate_start(unsigned long fid, struct smc_result *res)
{
	(void)fid;

	assert(fid == SMC_RMI_OP_MEM_RECLAIM);
	smmu_memory_reclaim(SRO_DEACTIVATE_FINISH, res);
}

/*
 * SRO handle callback for SMC_RMI_OP_CONTINUE during RMI_PSMMU_DEACTIVATE.
 */
void psmmu_deactivate_finish(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	struct sro_context *sro = my_sro_ctx();
	struct smmuv3_dev *smmu;

	/* Validate that this was invoked from RMI_OP_CONTINUE */
	assert(fid == SMC_RMI_OP_CONTINUE);
	assert(sro != NULL);

	smmu = sro->smmu_ctx.smmu_ptr;
	assert(smmu != NULL);

	smmuv3_psmmu_set_inactive(smmu);

	res->x[0] = RMI_SUCCESS;
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
void smc_psmmu_st_l2_create(unsigned long psmmu_ptr, unsigned long sid,
				struct smc_result *res)
{
	struct smmuv3_dev *smmu;
	struct sro_context *sro;
	unsigned long ret;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = RMI_ERROR_NOT_SUPPORTED;
		return;
	}

	smmu = smmuv3_psmmu_find(psmmu_ptr);
	if (smmu == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!smmuv3_psmmu_validate_sid(smmu, sid)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * Reserve an SRO context handle.
	 * The operaton cannot be cancelled.
	 * The requested memory is contiguous.
	 */
	ret = sro_ctx_reserve(SMC_RMI_PSMMU_ST_L2_CREATE, GRANULE_SIZE,
			      false, true, SMC_RMI_OP_MEM_DONATE);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);

	sro->smmu_ctx.smmu_ptr = smmu;
	sro->smmu_ctx.sid = sid;

	/* Prepare memory donation block for L2 Stream Table */
	sro->smmu_ctx.smmu_range[0].requested = 1UL;
	sro->smmu_ctx.smmu_range[0].contig = RMI_OP_MEM_CONTIG;

	smmu_prepare_donate(sro, SRO_CREATE_L2_START, res);
}

/**************************************************************************
 * Set of handler callbacks for RMI_PSMMU_CREATE_ST_L2.
 *
 * The following set of functions implement a state machine for
 * RMI_PSMMU_CREATE_ST_L2 and SRO support.
 **************************************************************************/
/*
 * SRO handle callback for RMI_OP_MEM_DONATE during RMI_PSMMU_CREATE_ST_L2.
 */
void psmmu_create_l2_start(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	struct sro_context *sro = my_sro_ctx();
	int ret;

	/* Validate that this was invoked from RMI_OP_MEM_DONATE */
	assert(fid == SMC_RMI_OP_MEM_DONATE);
	assert(sro != NULL);

	ret = smmu_memory_donate(sro, res);
	if (ret == 0) {
		/* Empty donation; request more memory from the host */
		return;
	}

	/* Return an error if memory donation fails */
	if (ret < 0) {
		/* Return the error from RMI_PSMMU_ST_L2_CREATE */
		sro->smmu_ctx.ret_err = RMI_ERROR_INPUT;

		/*
		 * Setup the callback for the next stage.
		 * There is nothing to reclaim, exit command with an error.
		 */
		sro->smmu_ctx.cb_id = (unsigned int)SRO_RECLAIM_FINISH;
		return;
	}

	/* Setup the callback for the next stage */
	sro->smmu_ctx.cb_id = (unsigned int)SRO_CREATE_L2_FINISH;

	/* RmiResult with RmiResultDataIncomplete */
	res->x[0] = (RMI_INCOMPLETE |
		     INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_NONE) |
		     INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL));
	res->x[2] = 0UL;
}

/*
 * SRO handle callback for RMI_OP_CONTINUE during RMI_PSMMU_ST_L2_CREATE.
 *
 * This callback is executed after all the necessary memory has been donated.
 */
void psmmu_create_l2_finish(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	struct sro_context *sro = my_sro_ctx();
	struct smmuv3_dev *smmu;
	unsigned long sid;
	int ret;

	/* Validate that this was invoked from RMI_OP_CONTINUE */
	assert(fid == SMC_RMI_OP_CONTINUE);
	assert(sro != NULL);

	smmu = sro->smmu_ctx.smmu_ptr;
	assert(smmu != NULL);

	sid = sro->smmu_ctx.sid;

	ret = smmuv3_psmmu_register_st_l2(smmu, sid, sro->smmu_ctx.smmu_range[0].base);
	if (ret == 0) {
		/* Finish the command with SUCCESS */
		res->x[0] = RMI_SUCCESS;
		return;
	}

	/*
	 * The command failed, so request the host to reclaim
	 * the donated memory and return.
	 */
	smmu_prepare_reclaim(sro, SRO_RECLAIM_START, RMI_ERROR_INPUT, false, res);
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
void smc_psmmu_st_l2_destroy(unsigned long psmmu_ptr, unsigned long sid,
				struct smc_result *res)
{
	struct smmuv3_dev *smmu;
	struct sro_context *sro;
	uintptr_t l2tab_pa;
	unsigned long ret;
	int rc;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = RMI_ERROR_NOT_SUPPORTED;
		return;
	}

	smmu = smmuv3_psmmu_find(psmmu_ptr);
	if (smmu == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!smmuv3_psmmu_validate_sid(smmu, sid)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}
	/*
	 * Reserve an SRO context handle.
	 * The operaton cannot be cancelled.
	 */
	ret = sro_ctx_reserve(SMC_RMI_PSMMU_ST_L2_DESTROY, 0UL,
			      false, true, SMC_RMI_OP_MEM_RECLAIM);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	rc = smmuv3_psmmu_release_st_l2(smmu, sid, &l2tab_pa);
	if (rc != 0) {
		res->x[0] = RMI_ERROR_INPUT;
		sro_ctx_release();
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);

	sro->smmu_ctx.smmu_ptr = smmu;
	sro->smmu_ctx.sid = sid;
	sro->smmu_ctx.smmu_range[0].requested = 1UL;
	sro->smmu_ctx.smmu_range[0].base = l2tab_pa;
	sro->smmu_ctx.range_idx = 0U;
	sro->smmu_ctx.total_transferred = 1UL;

	smmu_prepare_reclaim(sro, SRO_DESTROY_L2_START, RMI_SUCCESS, true, res);
}

/**************************************************************************
 * Set of handler callbacks for RMI_PSMMU_DESTROY_ST_L2.
 *
 * The following set of functions implement a state machine for
 * RMI_PSMMU_DESTROY_ST_L2 with SRO support.
 **************************************************************************/
/*
 * SRO handle callback for RMI_OP_MEM_RECLAIM.
 */
void psmmu_destroy_l2_start(unsigned long fid, struct smc_result *res)
{
	(void)fid;

	assert(fid == SMC_RMI_OP_MEM_RECLAIM);
	smmu_memory_reclaim(SRO_DESTROY_L2_FINISH, res);
}

/*
 * SRO handle callback for RMI_OP_CONTINUE during RMI_PSMMU_ST_L2_DESTROY.
 *
 * This callback is executed after all the necessary memory has been reclaimed.
 */
void psmmu_destroy_l2_finish(unsigned long fid, struct smc_result *res)
{
	(void)fid;

	/* Validate that this was invoked from RMI_OP_CONTINUE */
	assert(fid == SMC_RMI_OP_CONTINUE);
	res->x[0] = RMI_SUCCESS;
}

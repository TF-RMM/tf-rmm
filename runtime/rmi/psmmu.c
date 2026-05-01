/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <buffer.h>
#include <debug.h>
#include <feature.h>
#include <psmmu.h>
#include <psmmuv3.h>
#include <sro_context.h>
#include <xlat_defs.h>

static void activate_start(unsigned long fid, struct smc_result *res);
static void activate_finish(unsigned long fid, struct smc_result *res);
static void deactivate_start(unsigned long fid, struct smc_result *res);
static void deactivate_finish(unsigned long fid, struct smc_result *res);
static void create_l2_start(unsigned long fid, struct smc_result *res);
static void create_l2_continue(unsigned long fid, struct smc_result *res);
static void destroy_l2_start(unsigned long fid, struct smc_result *res);
static void destroy_l2_finish(unsigned long fid, struct smc_result *res);
static void reclaim_start(unsigned long fid, struct smc_result *res);
static void reclaim_finish(unsigned long fid, struct smc_result *res);

/*
 * Indices of PSMMU memory blocks
 */
/* L1 Stream Table */
#define	L1_ST_IDX	0U

/* L2 Stream Table descriptors */
#define	L2_DS_IDX	1U

/* SMMUv3 Command and Event queues */
#define QUEUE_IDX	2U

/*
 * Possible states of the SRO flow for RMI_PSMMU_CREATE_ST_L2
 * and RMI_PSMMU_ST_L2_DESTROY
 */
enum sro_psmmu_stage {
	SRO_ACTIVATE_START,
	SRO_ACTIVATE_FINISH,
	SRO_DEACTIVATE_START,
	SRO_DEACTIVATE_FINISH,
	SRO_CREATE_L2_START,
	SRO_CREATE_L2_CONTINUE,
	SRO_DESTROY_L2_START,
	SRO_DESTROY_L2_FINISH,
	SRO_RECLAIM_START,
	SRO_RECLAIM_FINISH,
	SRO_PSMMU_NUM_STATES
};

/* List of handlers that can be invoked from here */
static const sro_handle_cb sro_psmmu_callbacks[SRO_PSMMU_NUM_STATES] = {
	[SRO_ACTIVATE_START] = activate_start,
	[SRO_ACTIVATE_FINISH] = activate_finish,
	[SRO_DEACTIVATE_START] = deactivate_start,
	[SRO_DEACTIVATE_FINISH] = deactivate_finish,
	[SRO_CREATE_L2_START] = create_l2_start,
	[SRO_CREATE_L2_CONTINUE] = create_l2_continue,
	[SRO_DESTROY_L2_START] = destroy_l2_start,
	[SRO_DESTROY_L2_FINISH] = destroy_l2_finish,
	[SRO_RECLAIM_START] = reclaim_start,
	[SRO_RECLAIM_FINISH] = reclaim_finish,
};

/* cppcheck-suppress misra-c2012-8.7 */
void psmmu_continue_handler(unsigned long fid, struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();

	assert(sro != NULL);
	assert(sro->psmmu_ctx.cb_id < (unsigned int)SRO_PSMMU_NUM_STATES);

	sro_psmmu_callbacks[sro->psmmu_ctx.cb_id](fid, res);
}

static void prepare_donate(struct sro_context *sro, enum sro_psmmu_stage stage_id,
				struct smc_result *res)
{
	unsigned long contig = sro->psmmu_ctx.psmmu_block[0].contig;
	unsigned long requested = sro->psmmu_ctx.psmmu_block[0].requested;

	/*
	 * The first step will be to request the memory.
	 */
	sro->psmmu_ctx.cb_id = (unsigned int)stage_id;

	/* Initialize the SRO context for the command */
	sro->psmmu_ctx.block_idx = 0U;
	sro->psmmu_ctx.requested = requested;
	sro->psmmu_ctx.transferred = 0UL;
	sro->psmmu_ctx.total_transferred = 0UL;

	/* RmiResult with RmiResultDataIncomplete */
	res->x[0] = (RMI_INCOMPLETE |
			INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_DONATE) |
			INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL));

	/* RmiOpMemDonateReq */
	res->x[2] = (INPLACE(RMI_OP_DONATE_BLK_SIZE, RMI_PAGE_L3) |
		     INPLACE(RMI_OP_DONATE_BLK_COUNT, requested) |
		     INPLACE(RMI_OP_DONATE_MEM_CONTIG, contig) |
		     INPLACE(RMI_OP_DONATE_MEM_STATE, RMI_OP_MEM_DELEGATED));

	/* Seal the SRO context and get its handle */
	res->x[1] = sro_ctx_seal();
}

/* This function is called to start a memory reclaim of the memory donated */
static void prepare_reclaim(struct sro_context *sro, enum sro_psmmu_stage stage_id,
			    unsigned long err_code, bool seal_ctx, struct smc_result *res)
{
	/* Setup the callback for the next stage */
	sro->psmmu_ctx.cb_id = (unsigned int)stage_id;

	/* Initialize the SRO context for the command */
	sro->psmmu_ctx.total_transferred = 0UL;

	/* Log the error code from REC_CREATE */
	sro->psmmu_ctx.ret_err = err_code;

	/* RmiResult with RmiResultDataIncomplete */
	res->x[0] = (RMI_INCOMPLETE |
			INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_RECLAIM) |
			INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL));
	/*
	 * Seal the SRO context if requested, this happens
	 * when reclaim is started by top level SMC handler.
	 */
	if (seal_ctx) {
		res->x[1] = sro_ctx_seal();
	}
	res->x[2] = 0UL;
}

static int memory_donate(struct sro_context *sro, unsigned long contig,
			 struct smc_result *res)
{
	unsigned long donated = 0UL;
	unsigned long requested;
	unsigned long granule_pa;
	int block_level;
	unsigned long st;

	while (addr_list_reduce_first_block(&sro->addr_list,
					    &granule_pa,
					    &block_level,
					    &st)) {
		struct granule *donated_gr;

		/* This is checked by the SRO framework, assert the same */
		assert(st == RMI_OP_MEM_DELEGATED);

		/*
		 * Since we requested for granules which can be donated via L3 granules,
		 * assert the same.
		 * The SRO framework would have checked that total donated memory
		 * is <= requested memory.
		 */
		assert(block_level == 3);

		/* Try to transition the donated granule */
		donated_gr = find_lock_granule(granule_pa, GRANULE_STATE_DELEGATED);
		if (donated_gr == NULL) {
			return -1;
		}

		granule_unlock_transition(donated_gr, GRANULE_STATE_INTERNAL);

		donated++;

		/*
		 * Copy physical address of the donated granule.
		 * Increase the total number of granules donated.
		 */
		sro->psmmu_ctx.granules_pa[sro->psmmu_ctx.total_transferred++] = granule_pa;
	}

	res->x[1] = donated;

	sro->psmmu_ctx.transferred += donated;

	requested = sro->psmmu_ctx.requested;

	if (sro->psmmu_ctx.transferred < requested) {
		/* We need to request more granules */
		unsigned long pending = requested - sro->psmmu_ctx.transferred;

		res->x[0] = (RMI_INCOMPLETE |
				INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_DONATE) |
				INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL));

		/* RmiOpMemDonateReq */
		res->x[2] = (INPLACE(RMI_OP_DONATE_BLK_SIZE, RMI_PAGE_L3) |
			     INPLACE(RMI_OP_DONATE_BLK_COUNT, pending) |
			     INPLACE(RMI_OP_DONATE_MEM_CONTIG, contig) |
			     INPLACE(RMI_OP_DONATE_MEM_STATE, RMI_OP_MEM_DELEGATED));
		return 0;
	}

	/* All the memory has been donated */
	return 1;
}

/* This function is called to start a memory reclaim of the memory donated */
static void memory_reclaim(enum sro_psmmu_stage stage_id, struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	unsigned long to_reclaim;

	assert(sro != NULL);
	to_reclaim = sro->psmmu_ctx.requested;

	for (unsigned long i = 0UL; i < to_reclaim; i++) {
		unsigned long granule_pa = sro->psmmu_ctx.granules_pa[i];

		/* Transition the granule */
		struct granule *gr = find_lock_granule(granule_pa, GRANULE_STATE_INTERNAL);

		__unused bool ret;

		assert(gr != NULL);
		granule_unlock_transition_to_delegated(gr);

		/* Add the entry to the SRO addr list */
		ret = addr_list_add_block(&sro->addr_list, granule_pa, 3, RMI_OP_MEM_DELEGATED);
		assert(ret);
	}

	/* Setup the callback for the next stage */
	sro->psmmu_ctx.cb_id = (unsigned int)stage_id;

	/* RmiResult with RmiResultDataIncomplete */
	res->x[0] = (RMI_INCOMPLETE |
			INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_NONE) |
			INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL));
	res->x[1] = to_reclaim;
	res->x[2] = 0UL;
}

static void reclaim_start(unsigned long fid, struct smc_result *res)
{
	(void)fid;

	/* Validate that this was invoked from RMI_OP_RECLAIM */
	assert(fid == SMC_RMI_OP_MEM_RECLAIM);
	memory_reclaim(SRO_RECLAIM_FINISH, res);
}

static void reclaim_finish(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	struct sro_context *sro = my_sro_ctx();

	/* Validate that this was invoked from RMI_OP_CONTINUE */
	assert(fid == SMC_RMI_OP_CONTINUE);
	assert(sro != NULL);

	/* Return the error from RMI_PSMMU_ACTIVATE/RMI_PSMMU_ST_L2_CREATE */
	res->x[0] = sro->psmmu_ctx.ret_err;
	res->x[2] = 0UL;

	/* If called from RMI_PSMMU_ACTIVATE, set the state to PSMMU_INACTIVE */
	if (sro->psmmu_ctx.sid == UL(-1)) {
		psmmu_set_inactive(sro->psmmu_ctx.smmu_ptr);
	}
}

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
	unsigned long l1st_grans;
	unsigned long ret;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = RMI_ERROR_NOT_SUPPORTED;
		return;
	}

	smmu = psmmu_find(psmmu_ptr);
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
	if (!psmmu_validate_params(smmu, &params)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * Calculate the number of granules required for
	 * the L1 Stream Table and the array of L2 Stream
	 * Table descriptors.
	 */
	l1st_grans = psmmu_strtab_size(smmu) / GRANULE_SIZE;

	if (l1st_grans > SRO_PSMMU_L1_ST_GRANS) {
		ERROR("L1 Stream Table requires %lu granules,"
			"which exceeds the supported maximum of %u",
			l1st_grans, SRO_PSMMU_L1_ST_GRANS);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!psmmu_set_busy(smmu, PSMMU_INACTIVE)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

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
		psmmu_set_inactive(smmu);
		res->x[0] = ret;
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);

	sro->psmmu_ctx.smmu_ptr = smmu;
	sro->psmmu_ctx.sid = UL(-1);

	/* Prepare memory donation blocks */

	/* L1 Stream Table */
	sro->psmmu_ctx.psmmu_block[L1_ST_IDX].requested = l1st_grans;
	sro->psmmu_ctx.psmmu_block[L1_ST_IDX].contig = RMI_OP_MEM_CONTIG;

	/* L2 Descriptors */
	sro->psmmu_ctx.psmmu_block[L2_DS_IDX].requested = l1st_grans;
	sro->psmmu_ctx.psmmu_block[L2_DS_IDX].contig = RMI_OP_MEM_CONTIG;

	/* Command and Event queues */
	sro->psmmu_ctx.psmmu_block[QUEUE_IDX].requested = 2UL;
	sro->psmmu_ctx.psmmu_block[QUEUE_IDX].contig = RMI_OP_MEM_NON_CONTIG;

	prepare_donate(sro, SRO_ACTIVATE_START, res);
}

/**************************************************************************
 * Set of handler callbacks for RMI_PSMMU_ACTIVATE.
 *
 * The following set of static functions implement a state machine for
 * RMI_PSMMU_ACTIVATE and SRO support.
 **************************************************************************/
/*
 * SRO handle callback for RMI_OP_MEM_DONATE during RMI_PSMMU_ACTIVATE.
 */
static void activate_start(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	struct sro_context *sro = my_sro_ctx();
	unsigned long contig;
	unsigned int block_idx;
	int ret;

	/* Validate that this was invoked from RMI_OP_MEM_DONATE */
	assert(fid == SMC_RMI_OP_MEM_DONATE);
	assert(sro != NULL);

	/* Index of the granule to donate */
	block_idx = sro->psmmu_ctx.block_idx;

	/* Contiguous flag */
	contig = sro->psmmu_ctx.psmmu_block[block_idx].contig;

	ret = memory_donate(sro, contig, res);
	if (ret == 0) {
		return;
	}

	if (ret < 0) {
		/*
		 * The command failed, so request the host to reclaim
		 * the donated memory and return.
		 */
		sro->psmmu_ctx.requested = sro->psmmu_ctx.total_transferred;
		prepare_reclaim(sro, SRO_RECLAIM_START, RMI_ERROR_INPUT, false, res);
		return;
	}

	if (++block_idx < ARRAY_SIZE(sro->psmmu_ctx.psmmu_block)) {
		/* Next memory block */
		unsigned long requested = sro->psmmu_ctx.psmmu_block[block_idx].requested;

		contig = sro->psmmu_ctx.psmmu_block[block_idx].contig;

		/* Increase block index */
		sro->psmmu_ctx.block_idx = block_idx;

		/* Initialize the SRO context for the next interation */
		sro->psmmu_ctx.requested = requested;
		sro->psmmu_ctx.transferred = 0UL;

		/* RmiResult with RmiResultDataIncomplete */
		res->x[0] = (RMI_INCOMPLETE |
				INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_DONATE) |
				INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL));

		/* RmiOpMemDonateReq */
		res->x[2] = (
			INPLACE(RMI_OP_DONATE_BLK_SIZE, RMI_PAGE_L3) |
			INPLACE(RMI_OP_DONATE_BLK_COUNT, requested)  |
			INPLACE(RMI_OP_DONATE_MEM_CONTIG, contig)    |
			INPLACE(RMI_OP_DONATE_MEM_STATE, RMI_OP_MEM_DELEGATED));
		return;
	}

	/* Setup the callback for the next stage */
	sro->psmmu_ctx.cb_id = (unsigned int)SRO_ACTIVATE_FINISH;

	/* RmiResult with RmiResultDataIncomplete */
	res->x[0] = (RMI_INCOMPLETE |
		     INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_NONE) |
		     INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL));
	res->x[2] = 0UL;
}

/*
 * SRO handle callback for SMC_RMI_OP_CONTINUE during RMI_PSMMU_ACTIVATE.
 */
static void activate_finish(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	struct sro_context *sro = my_sro_ctx();
	struct smmuv3_dev *smmu;
	unsigned long num_granules;
	int ret;

	/* Validate that this was invoked from RMI_OP_CONTINUE */
	assert(fid == SMC_RMI_OP_CONTINUE);
	assert(sro != NULL);

	smmu = sro->psmmu_ctx.smmu_ptr;
	assert(smmu != NULL);

	res->x[2] = 0UL;

	ret = psmmu_register_st_l1(smmu, sro->psmmu_ctx.granules_pa);
	if (ret != 0) {
		goto reclaim;
	}

	ret = psmmu_register_queues(smmu);
	if (ret != 0) {
		goto reclaim;
	}

	/*
	 * Initialize and enable the SMMUv3 device.
	 * Set state to PSMMU_ACTIVE.
	 */
	if (psmmu_activate(smmu) == 0) {
		res->x[0] = RMI_SUCCESS;
		return;
	}

reclaim:
	sro->psmmu_ctx.smmu_ptr = smmu;
	sro->psmmu_ctx.sid = UL(-1);

	num_granules = psmmu_get_donated(smmu, sro->psmmu_ctx.granules_pa);
	sro->psmmu_ctx.requested = num_granules;

	prepare_reclaim(sro, SRO_RECLAIM_START, RMI_ERROR_INPUT, false, res);
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
	unsigned long num_granules, ret;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = RMI_ERROR_NOT_SUPPORTED;
		return;
	}

	smmu = psmmu_find(psmmu_ptr);
	if (smmu == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * Reserve an SRO context handle.
	 * The operaton cannot be cancelled.
	 * The requested memory is non-contiguous.
	 */
	ret = sro_ctx_reserve(SMC_RMI_PSMMU_DEACTIVATE, 0UL,
			      false, false, SMC_RMI_OP_MEM_RECLAIM);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	if (!psmmu_set_busy(smmu, PSMMU_ACTIVE)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (psmmu_deactivate(smmu) != 0) {
		/* Set the PSMMU state to PSMMU_INACTIVE */
		psmmu_set_inactive(smmu);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);

	sro->psmmu_ctx.smmu_ptr = smmu;
	sro->psmmu_ctx.sid = UL(-1);

	num_granules = psmmu_get_donated(smmu, sro->psmmu_ctx.granules_pa);
	sro->psmmu_ctx.requested = num_granules;

	prepare_reclaim(sro, SRO_DEACTIVATE_START, RMI_SUCCESS, true, res);
}

/**************************************************************************
 * Set of handler callbacks for RMI_PSMMU_DEACTIVATE.
 *
 * The following set of static functions implement a state machine for
 * RMI_PSMMU_DEACTIVATE and SRO support.
 **************************************************************************/

/*
 * SRO handle callback for SMC_RMI_OP_MEM_RECLAIM during RMI_PSMMU_DEACTIVATE.
 */
static void deactivate_start(unsigned long fid, struct smc_result *res)
{
	(void)fid;

	assert(fid == SMC_RMI_OP_MEM_RECLAIM);
	memory_reclaim(SRO_DEACTIVATE_FINISH, res);
}

/*
 * SRO handle callback for SMC_RMI_OP_CONTINUE during RMI_PSMMU_DEACTIVATE.
 */
static void deactivate_finish(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	struct sro_context *sro = my_sro_ctx();
	struct smmuv3_dev *smmu;

	/* Validate that this was invoked from RMI_OP_CONTINUE */
	assert(fid == SMC_RMI_OP_CONTINUE);
	assert(sro != NULL);

	smmu = sro->psmmu_ctx.smmu_ptr;
	assert(smmu != NULL);

	psmmu_set_inactive(smmu);

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

	smmu = psmmu_find(psmmu_ptr);
	if (smmu == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!psmmu_validate_sid(smmu, sid)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (psmmu_validate_st_l2(smmu, sid, NULL) != 0) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * Reserve an SRO context handle.
	 * The operaton cannot be cancelled.
	 * The requested memory is non-contiguous.
	 */
	ret = sro_ctx_reserve(SMC_RMI_PSMMU_ST_L2_CREATE, GRANULE_SIZE,
			      false, false, SMC_RMI_OP_MEM_DONATE);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);

	sro->psmmu_ctx.smmu_ptr = smmu;
	sro->psmmu_ctx.sid = sid;

	/* Prepare memory donation block for L2 Stream Table */
	sro->psmmu_ctx.psmmu_block[0].requested = 1UL;
	sro->psmmu_ctx.psmmu_block[0].contig = RMI_OP_MEM_NON_CONTIG;

	prepare_donate(sro, SRO_CREATE_L2_START, res);
}

/**************************************************************************
 * Set of handler callbacks for RMI_PSMMU_CREATE_ST_L2.
 *
 * The following set of static functions implement a state machine for
 * RMI_PSMMU_CREATE_ST_L2 and SRO support.
 **************************************************************************/
/*
 * SRO handle callback for RMI_OP_MEM_DONATE during RMI_PSMMU_CREATE_ST_L2.
 */
static void create_l2_start(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	struct sro_context *sro = my_sro_ctx();
	int ret;

	/* Validate that this was invoked from RMI_OP_MEM_DONATE */
	assert(fid == SMC_RMI_OP_MEM_DONATE);
	assert(sro != NULL);

	ret = memory_donate(sro, RMI_OP_MEM_NON_CONTIG, res);
	if (ret == 0) {
		return;
	}

	/* Return an error if memory donation fails */
	if (ret < 0) {
		/* Return the error from RMI_PSMMU_ST_L2_CREATE */
		sro->psmmu_ctx.ret_err = RMI_ERROR_INPUT;

		/*
		 * Setup the callback for the next stage.
		 * There is nothing to reclaim, exit command with an error.
		 */
		sro->psmmu_ctx.cb_id = (unsigned int)SRO_RECLAIM_FINISH;
		return;
	}

	/* Setup the callback for the next stage */
	sro->psmmu_ctx.cb_id = (unsigned int)SRO_CREATE_L2_CONTINUE;

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
static void create_l2_continue(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	struct sro_context *sro = my_sro_ctx();
	struct smmuv3_dev *smmu;
	unsigned long sid;
	int ret;

	/* Validate that this was invoked from RMI_OP_CONTINUE */
	assert(fid == SMC_RMI_OP_CONTINUE);
	assert(sro != NULL);

	smmu = sro->psmmu_ctx.smmu_ptr;
	assert(smmu != NULL);

	sid = sro->psmmu_ctx.sid;

	ret = psmmu_register_st_l2(smmu, sid, sro->psmmu_ctx.granules_pa[0]);
	if (ret == 0) {
		/* Finish the command with SUCCESS */
		res->x[0] = RMI_SUCCESS;
		res->x[2] = 0UL;
		return;
	}

	/*
	 * The command failed, so request the host to reclaim
	 * the donated memory and return.
	 */
	sro->psmmu_ctx.requested = 1UL;
	prepare_reclaim(sro, SRO_RECLAIM_START, RMI_ERROR_INPUT, false, res);
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

	smmu = psmmu_find(psmmu_ptr);
	if (smmu == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!psmmu_validate_sid(smmu, sid)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (psmmu_validate_st_l2(smmu, sid, &l2tab_pa) != 0) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	rc = psmmu_release_st_l2(smmu, sid);
	if (rc != 0) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * Reserve an SRO context handle.
	 * The operaton cannot be cancelled.
	 * The requested memory is non-contiguous.
	 */
	ret = sro_ctx_reserve(SMC_RMI_PSMMU_ST_L2_DESTROY, 0UL,
			      false, false, SMC_RMI_OP_MEM_RECLAIM);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);

	sro->psmmu_ctx.smmu_ptr = smmu;
	sro->psmmu_ctx.sid = sid;
	sro->psmmu_ctx.requested = 1UL;
	sro->psmmu_ctx.granules_pa[0] = l2tab_pa;

	prepare_reclaim(sro, SRO_DESTROY_L2_START, RMI_SUCCESS, true, res);
}

/**************************************************************************
 * Set of handler callbacks for RMI_PSMMU_DESTROY_ST_L2.
 *
 * The following set of static functions implement a state machine for
 * RMI_PSMMU_DESTROY_ST_L2 with SRO support.
 **************************************************************************/
/*
 * SRO handle callback for RMI_OP_MEM_RECLAIM.
 */
static void destroy_l2_start(unsigned long fid, struct smc_result *res)
{
	(void)fid;

	assert(fid == SMC_RMI_OP_MEM_RECLAIM);
	memory_reclaim(SRO_DESTROY_L2_FINISH, res);
}

/*
 * SRO handle callback for RMI_OP_CONTINUE during RMI_PSMMU_ST_L2_DESTROY.
 *
 * This callback is executed after all the necessary memory has been reclaimed.
 */
static void destroy_l2_finish(unsigned long fid, struct smc_result *res)
{
	(void)fid;

	/* Validate that this was invoked from RMI_OP_CONTINUE */
	assert(fid == SMC_RMI_OP_CONTINUE);
	res->x[0] = RMI_SUCCESS;
}


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

COMPILER_ASSERT(SRO_PSMMU_RANGES == (unsigned int)PSMMU_MEM_RANGE_NUM);

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
 * Possible states of the SRO flow for RMI_PSMMU_CREATE_ST_L2
 * and RMI_PSMMU_ST_L2_DESTROY
 */
enum psmmu_sro_stage {
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

static void prepare_donate(struct sro_context *sro, enum psmmu_sro_stage stage_id,
				struct smc_result *res)
{
	unsigned long contig = sro->psmmu_ctx.psmmu_range[0].contig;
	unsigned long requested = sro->psmmu_ctx.psmmu_range[0].requested;

	/*
	 * The first step will be to request the memory.
	 */
	sro->psmmu_ctx.cb_id = (unsigned int)stage_id;

	/* Initialize the SRO context for the command */
	sro->psmmu_ctx.range_idx = 0U;
	sro->psmmu_ctx.requested = requested;
	sro->psmmu_ctx.transferred = 0UL;
	sro->psmmu_ctx.total_transferred = 0UL;

	/* RmiResult with RmiResultDataIncomplete */
	res->x[0] = (RMI_INCOMPLETE |
			INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_DONATE) |
			INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL));

	/* RmiOpMemDonateReq */
	res->x[2] = rmi_op_donate_req_encode(requested * GRANULE_SIZE,
						     contig,
						     RMI_OP_MEM_DELEGATED);

	/* Seal the SRO context and get its handle */
	res->x[1] = sro_ctx_seal();
}

/* This function is called to start a memory reclaim of the memory donated */
static void prepare_reclaim(struct sro_context *sro, enum psmmu_sro_stage stage_id,
			    unsigned long err_code, bool seal_ctx, struct smc_result *res)
{
	/* Setup the callback for the next stage */
	sro->psmmu_ctx.cb_id = (unsigned int)stage_id;

	/* Log the error code */
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

/*
 * Process a single memory donation from the host for the current range.
 *
 * For contiguous donations (RMI_OP_MEM_CONTIG) the host supplies the entire
 * range as a single addr_list entry which may contain multiple blocks.
 * For non-contiguous donations (RMI_OP_MEM_NON_CONTIG) the host supplies
 * exactly one granule per addr_list.
 *
 * Each donated granule is transitioned from DELEGATED to INTERNAL state.
 * On failure mid-range the already-transitioned granules within that range
 * are rolled back inline (they cannot be tracked via psmmu_range[].base for later
 * reclaim).
 *
 * On success the base PA is recorded in psmmu_range[range_idx].base and the
 * transferred / total_transferred counters are updated.
 *
 * Parameters:
 *   sro - Pointer to SRO context.
 *   res - SMC result structure. On return:
 *         res->x[1] = number of granules donated this call.
 *         res->x[0], res->x[2] set when requesting more memory.
 *
 * Return:
 *    1  - All requested memory for this range has been donated.
 *    0  - Host sent an empty donation; RMM requests more via res->x[0..2].
 *   -1  - Granule transition failed; caller must trigger reclaim for all
 *         previously donated ranges.
 */
static int memory_donate(struct sro_context *sro, struct smc_result *res)
{
	unsigned long granule_pa, st;
	unsigned long num_grans, requested;
	unsigned long contig, pa;

	contig = sro->psmmu_ctx.psmmu_range[sro->psmmu_ctx.range_idx].contig;

	/*
	 * For a contiguous donation the host may supply the range as
	 * multiple blocks in single addr_list entry. Consume the whole
	 * contiguous range at once. For non-contiguous donations, the
	 * RMM requests one page per donation. So we expect to get only
	 * one page per addr_list.
	 */
	if (contig == RMI_OP_MEM_CONTIG) {
		unsigned long total_size;

		if (!addr_list_reduce_contig_block(&sro->addr_list,
						   &granule_pa,
						   &total_size,
						   &st)) {
			res->x[1] = 0UL;
			goto check_pending;
		}
		num_grans = total_size / GRANULE_SIZE;
	} else {
		int block_level;

		if (!addr_list_reduce_first_block(&sro->addr_list,
						  &granule_pa,
						  &block_level,
						  &st)) {
			res->x[1] = 0UL;
			goto check_pending;
		}
		num_grans = XLAT_BLOCK_SIZE(block_level) / GRANULE_SIZE;
	}

	assert(st == RMI_OP_MEM_DELEGATED);

	pa = granule_pa;

	/* Transition each granule within the range */
	for (unsigned long g = 0UL; g < num_grans; g++) {
		struct granule *donated_gr;

		donated_gr = find_lock_granule(pa, GRANULE_STATE_DELEGATED);
		if (donated_gr == NULL) {
			/*
			 * Roll back granules already transitioned within this range.
			 * A partial range cannot be tracked for reclaim.
			 */
			unsigned long rpa = granule_pa;

			for (unsigned long r = 0UL; r < g; r++) {
				struct granule *gr;

				gr = find_lock_granule(rpa, GRANULE_STATE_INTERNAL);
				assert(gr != NULL);
				granule_unlock_transition_to_delegated(gr);
				rpa += GRANULE_SIZE;
			}

			/* Trigger reclaim for all granules donated so far */
			return -1;
		}

		granule_unlock_transition(donated_gr, GRANULE_STATE_INTERNAL);

		/* Next granule */
		pa += GRANULE_SIZE;
	}

	/*
	 * Record the first PA as the base of the current range.
	 * The host donates the entire range in a single call
	 * (contig: whole block; non-contig: single granule),
	 * so transferred is always 0 here.
	 */
	assert(sro->psmmu_ctx.transferred == 0UL);
	sro->psmmu_ctx.psmmu_range[sro->psmmu_ctx.range_idx].base = granule_pa;

	res->x[1] = num_grans;
	sro->psmmu_ctx.transferred += num_grans;
	sro->psmmu_ctx.total_transferred += num_grans;

check_pending:
	requested = sro->psmmu_ctx.requested;

	/*
	 * A contiguous donation must deliver all requested memory in one go.
	 * If any granules were donated, the full amount must have arrived.
	 */
	assert((contig == RMI_OP_MEM_NON_CONTIG) ||
	       (sro->psmmu_ctx.transferred == 0UL) ||
	       (sro->psmmu_ctx.transferred == requested));

	if (sro->psmmu_ctx.transferred < requested) {
		/* We need to request more granules */
		unsigned long pending = requested - sro->psmmu_ctx.transferred;

		res->x[0] = (RMI_INCOMPLETE |
				INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_DONATE) |
				INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL));

		/* RmiOpMemDonateReq */
		res->x[2] = rmi_op_donate_req_encode(pending * GRANULE_SIZE,
						     contig,
						     RMI_OP_MEM_DELEGATED);
		return 0;
	}

	/* All the memory has been donated */
	return 1;
}

/* This function is called to start a memory reclaim of the memory donated */
static void memory_reclaim(enum psmmu_sro_stage stage_id, struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	unsigned long total, remaining;

	assert(sro != NULL);

	total = sro->psmmu_ctx.total_transferred;
	remaining = total;

	/*
	 * Reconstruct individual granule PAs from the base PA and size
	 * of each donated range, and transition each granule back to
	 * DELEGATED state. Use total_transferred to handle partial
	 * donations on the last range.
	 */
	for (unsigned int r = 0U; r <= sro->psmmu_ctx.range_idx; r++) {
		unsigned long count = sro->psmmu_ctx.psmmu_range[r].requested;
		uintptr_t granule_pa = sro->psmmu_ctx.psmmu_range[r].base;

		if (count > remaining) {
			count = remaining;
		}

		for (unsigned long j = 0UL; j < count; j++) {
			struct granule *gr;

			__unused bool ret;

			gr = find_lock_granule(granule_pa, GRANULE_STATE_INTERNAL);
			assert(gr != NULL);
			granule_unlock_transition_to_delegated(gr);

			ret = addr_list_add_block(&sro->addr_list, granule_pa,
					XLAT_TABLE_LEVEL_MAX,
					RMI_OP_MEM_DELEGATED);
			assert(ret);
			granule_pa += GRANULE_SIZE;
		}
		remaining -= count;
		if (remaining == 0UL) {
			break;
		}
	}

	/* Setup the callback for the next stage */
	sro->psmmu_ctx.cb_id = (unsigned int)stage_id;

	/* RmiResult with RmiResultDataIncomplete */
	res->x[0] = (RMI_INCOMPLETE |
			INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_NONE) |
			INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL));
	res->x[1] = total;
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
	 * the L1 Stream Table. The same size is used for
	 * the L2 Stream Table descriptors array.
	 */
	l1st_grans = psmmu_strtab_size(smmu) / GRANULE_SIZE;

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

	/* Prepare memory donation ranges */

	/* L1 Stream Table */
	sro->psmmu_ctx.psmmu_range[(unsigned int)PSMMU_MEM_RANGE_L1_ST].requested = l1st_grans;
	sro->psmmu_ctx.psmmu_range[(unsigned int)PSMMU_MEM_RANGE_L1_ST].contig =
									RMI_OP_MEM_CONTIG;
	/* L2 Stream Table descriptors array */
	/*
	 * TODO: currently we request a contiguous block, but this needs
	 * to be changed to non-contiguous.
	 */
	sro->psmmu_ctx.psmmu_range[(unsigned int)PSMMU_MEM_RANGE_L2_DS].requested = l1st_grans;
	sro->psmmu_ctx.psmmu_range[(unsigned int)PSMMU_MEM_RANGE_L2_DS].contig =
									RMI_OP_MEM_CONTIG;
	/* Command queue */
	sro->psmmu_ctx.psmmu_range[(unsigned int)PSMMU_MEM_RANGE_CMDQ].requested = 1UL;
	sro->psmmu_ctx.psmmu_range[(unsigned int)PSMMU_MEM_RANGE_CMDQ].contig =
									RMI_OP_MEM_NON_CONTIG;
	/* Event queue */
	sro->psmmu_ctx.psmmu_range[(unsigned int)PSMMU_MEM_RANGE_EVTQ].requested = 1UL;
	sro->psmmu_ctx.psmmu_range[(unsigned int)PSMMU_MEM_RANGE_EVTQ].contig =
									RMI_OP_MEM_NON_CONTIG;
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
	unsigned int range_idx;
	int ret;

	/* Validate that this was invoked from RMI_OP_MEM_DONATE */
	assert(fid == SMC_RMI_OP_MEM_DONATE);
	assert(sro != NULL);

	ret = memory_donate(sro, res);
	if (ret == 0) {
		/* Empty donation; request more memory from the host */
		return;
	}

	if (ret < 0) {
		/*
		 * The command failed, so request the host to reclaim
		 * the donated memory and return.
		 */
		prepare_reclaim(sro, SRO_RECLAIM_START, RMI_ERROR_INPUT, false, res);
		return;
	}

	/* Index of the range to donate */
	range_idx = sro->psmmu_ctx.range_idx;

	if (++range_idx < (unsigned int)PSMMU_MEM_RANGE_NUM) {
		/* Next memory range */
		unsigned long requested = sro->psmmu_ctx.psmmu_range[range_idx].requested;
		unsigned long contig = sro->psmmu_ctx.psmmu_range[range_idx].contig;

		sro->psmmu_ctx.range_idx = range_idx;

		/* Initialize the SRO context for the next interation */
		sro->psmmu_ctx.requested = requested;
		sro->psmmu_ctx.transferred = 0UL;

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
	int ret;

	/* Validate that this was invoked from RMI_OP_CONTINUE */
	assert(fid == SMC_RMI_OP_CONTINUE);
	assert(sro != NULL);

	smmu = sro->psmmu_ctx.smmu_ptr;
	assert(smmu != NULL);

	res->x[2] = 0UL;

	ret = psmmu_register_st_l1(smmu,
			sro->psmmu_ctx.psmmu_range[(unsigned int)PSMMU_MEM_RANGE_L1_ST].base,
			sro->psmmu_ctx.psmmu_range[(unsigned int)PSMMU_MEM_RANGE_L2_DS].base);
	if (ret != 0) {
		goto unmap_reclaim;
	}

	ret = psmmu_register_queues(smmu,
			sro->psmmu_ctx.psmmu_range[(unsigned int)PSMMU_MEM_RANGE_CMDQ].base,
			sro->psmmu_ctx.psmmu_range[(unsigned int)PSMMU_MEM_RANGE_EVTQ].base);
	if (ret != 0) {
		goto unmap_reclaim;
	}

	/*
	 * Initialize and enable the SMMUv3 device.
	 * Set state to PSMMU_ACTIVE.
	 */
	ret = psmmu_activate(smmu);
	if (ret == 0) {
		res->x[0] = RMI_SUCCESS;
		return;
	}

unmap_reclaim:
	psmmu_unmap(smmu);
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
	uintptr_t bases[SRO_PSMMU_RANGES];
	unsigned long sizes[SRO_PSMMU_RANGES];
	unsigned long total = 0UL;
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

	if (!psmmu_set_busy(smmu, PSMMU_ACTIVE)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * Reserve an SRO context handle.
	 * The operaton cannot be cancelled.
	 */
	ret = sro_ctx_reserve(SMC_RMI_PSMMU_DEACTIVATE, 0UL,
			      false, false, SMC_RMI_OP_MEM_RECLAIM);
	if (ret != RMI_SUCCESS) {
		psmmu_set_active(smmu);
		res->x[0] = ret;
		return;
	}

	if (psmmu_deactivate(smmu) != 0) {
		psmmu_set_active(smmu);
		sro_ctx_release();
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);

	sro->psmmu_ctx.smmu_ptr = smmu;
	sro->psmmu_ctx.sid = UL(-1);

	/*
	 * Retrieve the base PA and size of each donated range from the
	 * driver. memory_reclaim() will reconstruct individual granule
	 * PAs from these.
	 */
	psmmu_get_donated(smmu, bases, sizes);

	for (unsigned int i = 0U; i < (unsigned int)PSMMU_MEM_RANGE_NUM; i++) {
		sro->psmmu_ctx.psmmu_range[i].base = bases[i];
		sro->psmmu_ctx.psmmu_range[i].requested = sizes[i];
		total += sizes[i];
	}
	sro->psmmu_ctx.total_transferred = total;
	sro->psmmu_ctx.range_idx = (unsigned int)PSMMU_MEM_RANGE_NUM - 1U;

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
	sro->psmmu_ctx.psmmu_range[0].requested = 1UL;
	sro->psmmu_ctx.psmmu_range[0].contig = RMI_OP_MEM_NON_CONTIG;

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

	ret = memory_donate(sro, res);
	if (ret == 0) {
		/* Empty donation; request more memory from the host */
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

	ret = psmmu_register_st_l2(smmu, sid, sro->psmmu_ctx.psmmu_range[0].base);
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
	/*
	 * Reserve an SRO context handle.
	 * The operaton cannot be cancelled.
	 */
	ret = sro_ctx_reserve(SMC_RMI_PSMMU_ST_L2_DESTROY, 0UL,
			      false, false, SMC_RMI_OP_MEM_RECLAIM);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	rc = psmmu_release_st_l2(smmu, sid, &l2tab_pa);
	if (rc != 0) {
		res->x[0] = RMI_ERROR_INPUT;
		sro_ctx_release();
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);

	sro->psmmu_ctx.smmu_ptr = smmu;
	sro->psmmu_ctx.sid = sid;
	sro->psmmu_ctx.psmmu_range[0].requested = 1UL;
	sro->psmmu_ctx.psmmu_range[0].base = l2tab_pa;
	sro->psmmu_ctx.range_idx = 0U;
	sro->psmmu_ctx.total_transferred = 1UL;

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


/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <assert.h>
#include <granule.h>
#include <psmmu.h>
#include <smmuv3_psmmu.h>
#include <sro_context.h>
#include <sro_smmu.h>

COMPILER_ASSERT(SRO_SMMU_RANGES == (unsigned int)PSMMU_MEM_RANGE_NUM);

/* List of handlers that can be invoked from here */
static const sro_handle_cb sro_smmu_callbacks[SRO_SMMU_NUM_STATES] = {
	[SRO_ACTIVATE_START] = psmmu_activate_start,
	[SRO_ACTIVATE_FINISH] = psmmu_activate_finish,
	[SRO_DEACTIVATE_START] = psmmu_deactivate_start,
	[SRO_DEACTIVATE_FINISH] = psmmu_deactivate_finish,
	[SRO_CREATE_L2_START] = psmmu_create_l2_start,
	[SRO_CREATE_L2_FINISH] = psmmu_create_l2_finish,
	[SRO_DESTROY_L2_START] = psmmu_destroy_l2_start,
	[SRO_DESTROY_L2_FINISH] = psmmu_destroy_l2_finish,
	[SRO_RECLAIM_START] = smmu_reclaim_start,
	[SRO_RECLAIM_FINISH] = smmu_reclaim_finish
};

/* cppcheck-suppress misra-c2012-8.7 */
void smmu_continue_handler(unsigned long fid, struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();

	assert(sro != NULL);
	assert(sro->smmu_ctx.cb_id < (unsigned int)SRO_SMMU_NUM_STATES);

	sro_smmu_callbacks[sro->smmu_ctx.cb_id](fid, res);
}

void smmu_prepare_donate(struct sro_context *sro, enum smmu_sro_stage stage_id,
			 struct smc_result *res)
{
	unsigned long contig = sro->smmu_ctx.smmu_range[0].contig;
	unsigned long requested = sro->smmu_ctx.smmu_range[0].requested;

	/*
	 * The first step will be to request the memory.
	 */
	sro->smmu_ctx.cb_id = (unsigned int)stage_id;

	/* Initialize the SRO context for the command */
	sro->smmu_ctx.range_idx = 0U;
	sro->smmu_ctx.requested = requested;
	sro->smmu_ctx.transferred = 0UL;
	sro->smmu_ctx.total_transferred = 0UL;

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
void smmu_prepare_reclaim(struct sro_context *sro, enum smmu_sro_stage stage_id,
			  unsigned long err_code, bool seal_ctx, struct smc_result *res)
{
	/* Setup the callback for the next stage */
	sro->smmu_ctx.cb_id = (unsigned int)stage_id;

	/* Log the error code */
	sro->smmu_ctx.ret_err = err_code;

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
 * are rolled back inline (they cannot be tracked via smmu_range[].base for later
 * reclaim).
 *
 * On success the base PA is recorded in smmu_range[range_idx].base and the
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
int smmu_memory_donate(struct sro_context *sro, struct smc_result *res)
{
	unsigned long granule_pa, st;
	unsigned long num_grans, requested;
	unsigned long contig, pa;

	contig = sro->smmu_ctx.smmu_range[sro->smmu_ctx.range_idx].contig;

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
	assert(sro->smmu_ctx.transferred == 0UL);
	sro->smmu_ctx.smmu_range[sro->smmu_ctx.range_idx].base = granule_pa;

	res->x[1] = num_grans;
	sro->smmu_ctx.transferred += num_grans;
	sro->smmu_ctx.total_transferred += num_grans;

check_pending:
	requested = sro->smmu_ctx.requested;

	/*
	 * A contiguous donation must deliver all requested memory in one go.
	 * If any granules were donated, the full amount must have arrived.
	 */
	assert((contig == RMI_OP_MEM_NON_CONTIG) ||
	       (sro->smmu_ctx.transferred == 0UL) ||
	       (sro->smmu_ctx.transferred == requested));

	if (sro->smmu_ctx.transferred < requested) {
		/* We need to request more granules */
		unsigned long pending = requested - sro->smmu_ctx.transferred;

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
void smmu_memory_reclaim(enum smmu_sro_stage stage_id, struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	unsigned long total, remaining;

	assert(sro != NULL);

	total = sro->smmu_ctx.total_transferred;
	remaining = total;

	/*
	 * Reconstruct individual granule PAs from the base PA and size of each
	 * donated range, and transition each granule back to DELEGATED state.
	 * Use total_transferred to handle partial donations on the last range.
	 */
	for (unsigned int r = 0U; r <= sro->smmu_ctx.range_idx; r++) {
		unsigned long count = sro->smmu_ctx.smmu_range[r].requested;
		uintptr_t granule_pa = sro->smmu_ctx.smmu_range[r].base;

		if (count > remaining) {
			count = remaining;
		}

		for (unsigned long j = 0UL; j < count; j++) {
			struct granule *gr;
			bool add_ret __unused;

			gr = find_lock_granule(granule_pa,
						GRANULE_STATE_INTERNAL);
			assert(gr != NULL);
			granule_unlock_transition_to_delegated(gr);

			add_ret = addr_list_add_block(
					&sro->addr_list, granule_pa,
					XLAT_TABLE_LEVEL_MAX,
					RMI_OP_MEM_DELEGATED);
			assert(add_ret);
			granule_pa += GRANULE_SIZE;
		}

		remaining -= count;
		if (remaining == 0UL) {
			break;
		}
	}

	/* Setup the callback for the next stage */
	sro->smmu_ctx.cb_id = (unsigned int)stage_id;

	/* RmiResult with RmiResultDataIncomplete */
	res->x[0] = (RMI_INCOMPLETE |
			INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_NONE) |
			INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL));
	res->x[1] = total;
	res->x[2] = 0UL;
}

void smmu_reclaim_start(unsigned long fid, struct smc_result *res)
{
	(void)fid;

	/* Validate that this was invoked from RMI_OP_RECLAIM */
	assert(fid == SMC_RMI_OP_MEM_RECLAIM);
	smmu_memory_reclaim(SRO_RECLAIM_FINISH, res);
}

void smmu_reclaim_finish(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	struct sro_context *sro = my_sro_ctx();

	/* Validate that this was invoked from RMI_OP_CONTINUE */
	assert(fid == SMC_RMI_OP_CONTINUE);
	assert(sro != NULL);

	/* Return the error from RMI_PSMMU_ACTIVATE/RMI_PSMMU_ST_L2_CREATE */
	res->x[0] = sro->smmu_ctx.ret_err;
	res->x[2] = 0UL;

	/* If called from RMI_PSMMU_ACTIVATE, set the state to PSMMU_INACTIVE */
	if (sro->smmu_ctx.sid == UL(-1)) {
		smmuv3_psmmu_set_inactive(sro->smmu_ctx.smmu_ptr);
	}
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <granule.h>
#include <sro_context.h>
#include <utils_def.h>

static void sro_aux_granule_return_to_delegated(unsigned long granule_pa,
						unsigned char aux_granule_state)
{
	struct granule *gr;

	gr = find_lock_granule(granule_pa, aux_granule_state);
	assert(gr != NULL);
	granule_unlock_transition_to_delegated(gr);
}

/*
 * SRO handle callback to finish a SRO reclaim flow with the stored RmiResult.
 */
/* cppcheck-suppress misra-c2012-8.7 */
void sro_aux_op_reclaim_finish(unsigned long fid, struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	struct granule *gr;

	(void)fid;

	assert(sro != NULL);

	/*
	 * At this point, all the memory has been successfully reclaimed
	 * and communicated to NS Host. Return the partially destroyed object
	 * granule to DELEGATED.
	 */
	gr = find_lock_granule(sro->aux_op_ctx.obj_addr, GRANULE_STATE_PARTIAL);
	assert(gr != NULL);
	granule_unlock_transition_to_delegated(gr);

	/* Return the error code from object create/destroy */
	res->x[0] = sro->aux_op_ctx.ret_err;
	res->x[2] = 0UL;
}

/*
 * SRO handle callback for RMI_OP_MEM_RECLAIM.
 */
/* cppcheck-suppress misra-c2012-8.7 */
void sro_obj_memory_reclaim(unsigned long fid, struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	unsigned long to_reclaim;

	assert(sro != NULL);
	assert(fid == SMC_RMI_OP_MEM_RECLAIM);

	(void)fid;

	to_reclaim = MIN(sro->aux_op_ctx.requested_aux_granules,
			sro_ctx_range_desc_count(sro));

	for (unsigned long i = 0UL; i < to_reclaim; i++) {
		bool ret __unused;

		unsigned long granule_idx = i + sro->aux_op_ctx.total_transferred;

		assert(granule_idx < ARRAY_SIZE(sro->aux_op_ctx.aux_granules_pa));
		unsigned long granule_pa = sro->aux_op_ctx.aux_granules_pa[granule_idx];

		/* Transition the granule */
		sro_aux_granule_return_to_delegated(granule_pa, sro->aux_op_ctx.aux_granule_state);

		/* Add the entry to the SRO addr list */
		ret = addr_list_add_block(&sro->addr_list, granule_pa, 3, RMI_OP_MEM_DELEGATED);
		assert(ret);
	}

	sro->aux_op_ctx.requested_aux_granules -= to_reclaim;
	sro->aux_op_ctx.total_transferred += to_reclaim;

	/* RmiResult with RmiResultDataIncomplete */
	res->x[0] = (RMI_INCOMPLETE |
			INPLACE(RMI_OP_CAN_CANCEL_BIT, SRO_CAN_CANCEL_FLAG(sro)));

	if (sro->aux_op_ctx.requested_aux_granules == 0UL) {
		/* All granules added to the reclaim list */
		res->x[0] |= INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_NONE);

		/* Setup the callback for the next stage */
		sro->aux_op_ctx.cb_id = SRO_OBJ_DESTROY_FINISH;
	} else {
		res->x[0] |= INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_RECLAIM);

		/* Setup the callback for the next stage */
		sro->aux_op_ctx.cb_id = SRO_OBJ_MEM_RECLAIM;
	}

	res->x[1] = to_reclaim;
	res->x[2] = 0UL;
}

/*
 * SRO handle callback for RMI_OP_MEM_DONATE during object creation.
 */
/* cppcheck-suppress misra-c2012-8.7 */
void sro_obj_memory_donate(unsigned long fid, struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	unsigned long donated_granules = 0UL;
	unsigned long granule_pa;
	int block_level;
	unsigned long st;

	assert(sro != NULL);
	(void)fid;

	/* Validate that this was invoked from RMI_OP_MEM_DONATE */
	assert(fid == SMC_RMI_OP_MEM_DONATE);

	while (addr_list_reduce_first_block(&sro->addr_list,
						      &granule_pa,
						      &block_level,
						      &st)) {
		struct granule *donated_gr;

		/* This is checked by the SRO framework, assert the same. */
		assert(st == RMI_OP_MEM_DELEGATED);
		/*
		 * Since we requested for granules which can be donated via
		 * L3 granules, assert the same. The SRO framework would have
		 * checked that total donated memory is <= requested memory.
		 */
		assert(block_level == 3);

		/* Try to transition the donated granule */
		donated_gr = find_lock_granule(granule_pa, GRANULE_STATE_DELEGATED);


		if (donated_gr == NULL) {
			if (donated_granules == 0UL) {
				/*
				 * Failed on the very first granule in the list.
				 * Return an error so the host knows the list is
				 * invalid rather than requesting more donations.
				 */
				sro_aux_op_start_reclaim(sro, res,
					sro->aux_op_ctx.obj_addr,
					false,
					RMI_ERROR_INPUT, sro->aux_op_ctx.total_transferred,
					sro->aux_op_ctx.aux_granule_state);
				return;
			}
			/* We cannot transition this granule, so stop here */
			break;
		}

		granule_unlock_transition(donated_gr, sro->aux_op_ctx.aux_granule_state);

		assert((donated_granules + sro->aux_op_ctx.total_transferred) <
			ARRAY_SIZE(sro->aux_op_ctx.aux_granules_pa));
		sro->aux_op_ctx.aux_granules_pa[
			donated_granules + sro->aux_op_ctx.total_transferred] = granule_pa;

		donated_granules++;
	}


	/* Record the number of granules we have so far */
	sro->aux_op_ctx.total_transferred += donated_granules;

	if (sro->aux_op_ctx.total_transferred <
			sro->aux_op_ctx.requested_aux_granules) {
		/* We need to request more granules */
		unsigned long pending = sro->aux_op_ctx.requested_aux_granules
					- sro->aux_op_ctx.total_transferred;

		 /* RmiResult with RmiResultDataIncomplete */
		res->x[0] = (RMI_INCOMPLETE |
				INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_DONATE) |
				INPLACE(RMI_OP_CAN_CANCEL_BIT, SRO_CAN_CANCEL_FLAG(sro)));

		/* RmiOpMemDonateReq */
		res->x[2] = rmi_op_donate_req_encode(
					pending * GRANULE_SIZE,
					SRO_CONTIG_FLAG(sro),
					RMI_OP_MEM_DELEGATED);

		sro->aux_op_ctx.cb_id = SRO_OBJ_MEM_DONATE;
	} else {
		/* All the memory has been donated */

		/* RmiResult with RmiResultDataIncomplete */
		res->x[0] = (RMI_INCOMPLETE |
				INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_NONE) |
				INPLACE(RMI_OP_CAN_CANCEL_BIT, SRO_CAN_CANCEL_FLAG(sro)));

		res->x[2] = 0UL;

		/* Setup the callback for the next stage */
		sro->aux_op_ctx.cb_id = SRO_OBJ_CREATE_CONTINUE;
	}

	res->x[1] = donated_granules;
}

/* cppcheck-suppress misra-c2012-8.7 */
void sro_aux_op_init_donate(struct sro_context *sro,
			    struct smc_result *res,
			    unsigned long obj_addr,
			    unsigned long requested_aux_granules,
			    unsigned char aux_granule_state)
{
	struct sro_aux_op_ctx *ctx;

	assert(sro != NULL);
	assert(res != NULL);

	ctx = &sro->aux_op_ctx;
	ctx->cb_id = SRO_OBJ_MEM_DONATE;
	ctx->requested_aux_granules = requested_aux_granules;
	ctx->aux_granule_state = aux_granule_state;
	ctx->total_transferred = 0UL;
	ctx->obj_addr = obj_addr;

	res->x[0] = (RMI_INCOMPLETE |
		     INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_DONATE) |
		     INPLACE(RMI_OP_CAN_CANCEL_BIT, SRO_CAN_CANCEL_FLAG(sro)));
	res->x[2] = (INPLACE(RMI_OP_DONATE_BLK_SIZE, RMI_PAGE_L3) |
		     INPLACE(RMI_OP_DONATE_BLK_COUNT, ctx->requested_aux_granules) |
		     INPLACE(RMI_OP_DONATE_MEM_CONTIG, SRO_CONTIG_FLAG(sro)) |
		     INPLACE(RMI_OP_DONATE_MEM_STATE, RMI_OP_MEM_DELEGATED));
	res->x[1] = sro_ctx_seal();
}

void sro_aux_op_start_reclaim(struct sro_context *sro,
			      struct smc_result *res,
			      unsigned long obj_addr,
			      bool seal_ctx,
			      unsigned long err_code,
			      unsigned long num_granules,
			      unsigned char aux_granule_state)
{
	struct sro_aux_op_ctx *ctx = &sro->aux_op_ctx;

	assert(sro != NULL);
	assert(ctx != NULL);
	assert(res != NULL);

	ctx->obj_addr = obj_addr;

	/* Assert that the obj granule state is PARTIAL */
	assert(granule_unlocked_state(find_granule(ctx->obj_addr))
		== GRANULE_STATE_PARTIAL);

	/* Setup the callback for the next stage */
	ctx->cb_id = SRO_OBJ_MEM_RECLAIM;
	/* Log the error code from object create function */
	ctx->ret_err = err_code;

	ctx->requested_aux_granules = num_granules;
	ctx->total_transferred = 0UL;
	ctx->aux_granule_state = aux_granule_state;

	/* RmiResult with RmiResultDataIncomplete */
	res->x[0] = (RMI_INCOMPLETE |
		     INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_RECLAIM) |
		     INPLACE(RMI_OP_CAN_CANCEL_BIT, SRO_CAN_CANCEL_FLAG(sro)));
	res->x[1] = 0UL;
	res->x[2] = 0UL;

	/*
	 * Seal the SRO context if requested, this happens
	 * when reclaim is started by top level SMC handler.
	 */
	if (seal_ctx) {
		res->x[1] = sro_ctx_seal();
	}
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <addr_list.h>
#include <assert.h>
#include <buffer.h>
#include <debug.h>
#include <granule.h>
#include <granule_types.h>
#include <limits.h>
#include <rec.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <sro_context.h>
#include <status.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>
#include <utils_def.h>
#include <xlat_defs.h>

struct rmi_handles {
	sro_handle_cb cb;
};

#define SRO_HANDLE(_id, _cb)[RMI_HANDLER_ID(SMC_RMI_##_id)] = {		\
	.cb = (_cb)							\
}

static struct rmi_handles sro_handles[] = {
	SRO_HANDLE(REC_CREATE, rec_continue_handler),
	SRO_HANDLE(REC_DESTROY, rec_continue_handler)
};
COMPILER_ASSERT(ARRAY_SIZE(sro_handles) <= SMC64_NUM_FIDS_IN_RANGE(RMI));

/*
 * ONLY FOR TESTING PURPOSES
 * Install a test callback for a given SRO command.
 *
 * This allows unit tests to exercise smc_op_mem_donate() and other SRO
 * entry points in isolation without going through the full REC_CREATE /
 * REC_DESTROY flows.
 *
 * Returns the previous callback so the caller can restore it.
 */
/* coverity[misra_c_2012_rule_8_4_violation:SUPPRESS] */
sro_handle_cb sro_install_test_handler(unsigned long command, sro_handle_cb cb)
{
	unsigned long idx = RMI_HANDLER_ID(command);

	assert(idx < ARRAY_SIZE(sro_handles));

	sro_handle_cb old = sro_handles[idx].cb;

	sro_handles[idx].cb = cb;
	return old;
}

static void rmi_op_dispatch(unsigned long fid,
			    struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	unsigned long handle_id;

	assert(sro != NULL);

	handle_id = RMI_HANDLER_ID(sro->init_command);
	assert(handle_id < ARRAY_SIZE(sro_handles));
	assert(sro_handles[handle_id].cb != NULL);

	assert((fid == SMC_RMI_OP_CANCEL) || (sro->expected_fid == fid));

	sro_handles[handle_id].cb(fid, res);

	if (unpack_return_code(res->x[0]).status == RMI_INCOMPLETE) {
		unsigned long mem_op = EXTRACT(RMI_OP_MEM_REQ, res->x[0]);

		/* Update the memory flags on the SRO context if needed */
		sro->can_cancel = (EXTRACT(RMI_OP_CAN_CANCEL_BIT, res->x[0]) ==
								RMI_OP_CAN_CANCEL);

		if (mem_op == RMI_OP_MEM_REQ_DONATE) {
			sro->transfer_req = RMI_OP_DONATE_TRANSFER_SIZE(res->x[2]);
			sro->is_contig =
				(EXTRACT(RMI_OP_DONATE_MEM_CONTIG, res->x[2]) ==
							RMI_OP_MEM_CONTIG);

			sro->mem_state =
				(EXTRACT(RMI_OP_DONATE_MEM_STATE, res->x[2]) ==
							RMI_OP_MEM_DELEGATED) ?
							RMI_OP_MEM_DELEGATED :
							RMI_OP_MEM_UNDELEGATED;
		}

		/*
		 * Derive expected_fid from the callback result.
		 * This must happen before saving prev_exp_fid so
		 * the saved value reflects the post-operation intent.
		 */
		if (mem_op == RMI_OP_MEM_REQ_DONATE) {
			sro->expected_fid = SMC_RMI_OP_MEM_DONATE;
		} else if (mem_op == RMI_OP_MEM_REQ_RECLAIM) {
			sro->expected_fid = SMC_RMI_OP_MEM_RECLAIM;
		} else {
			assert(mem_op == RMI_OP_MEM_REQ_NONE);
			sro->expected_fid = SMC_RMI_OP_CONTINUE;
		}

		if ((mem_op == RMI_OP_MEM_REQ_RECLAIM) ||
			((fid == SMC_RMI_OP_MEM_RECLAIM) &&
			(res->x[1] > 0UL))) {

			assert((mem_op == RMI_OP_MEM_REQ_RECLAIM) || (mem_op == RMI_OP_MEM_REQ_NONE));

			/*
			 * Reclaim cb result. Also handle the case where
			 * all entries fit in one batch (MEM_REQ_NONE) but
			 * still need to be copied to NS memory.
			 */
			sro->reclaim_res = res->x[0];
			sro->prev_exp_fid = sro->expected_fid;
		}
	} else {
		/* BUSY or terminal (SUCCESS, ERROR) → expect CONTINUE */
		sro->expected_fid = SMC_RMI_OP_CONTINUE;
	}
}

void smc_op_mem_donate(unsigned long handle,
			unsigned long list_addr,
			unsigned long list_count,
			struct smc_result *res)
{
	bool found;
	struct sro_context *sro;
	unsigned long list_offset;
	unsigned long total_mem = 0UL;

	found = sro_ctx_find(handle);
	if (!found) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);

	if (sro->expected_fid != SMC_RMI_OP_MEM_DONATE) {
		res->x[0] = RMI_ERROR_INPUT;
		goto donate_end;
	}

	if (!ALIGNED(list_addr, sizeof(unsigned long))) {
		res->x[0] = RMI_ERROR_INPUT;
		goto donate_end;
	}

	addr_list_init(&sro->addr_list, LIST_TYPE_INPUT);

	/*
	 * The list can start at any place inside a given granule (provided
	 * that is aligned to 8 bytes).
	 *
	 * Calculate the offset of the first entry with regards to the start
	 * of the granule where the list is.
	 */
	list_offset = (list_addr & ~GRANULE_MASK) / sizeof(unsigned long);

	/*
	 * Limit the number of entries to not cross granules.
	 * The command will terminate with INCOMPLETE if there is a granule cross.
	 * Cap list_count before the addition to prevent integer overflow.
	 */
	list_count = MIN(list_count, ADDR_LIST_MAX_RANGES);
	list_count = (((list_count + list_offset) > ADDR_LIST_MAX_RANGES) ?
				(ADDR_LIST_MAX_RANGES - list_offset) : list_count);

	if (!addr_list_copy_from_host(&sro->addr_list, list_addr, (unsigned int)list_count)) {
		res->x[0] = RMI_ERROR_INPUT;
		goto donate_end;
	}

	/* Validate the copied addr_list */
	if (!addr_list_validate(&sro->addr_list, sro->is_contig, &total_mem,
			sro->mem_state)) {
		res->x[0] = RMI_ERROR_INPUT;
		goto donate_end;
	}

	if (total_mem > sro->transfer_req) {
		res->x[0] = RMI_ERROR_INPUT;
		goto donate_end;
	}

	sro->range_desc_count = list_count;
	rmi_op_dispatch(SMC_RMI_OP_MEM_DONATE, res);
	assert((res->x[1] * GRANULE_SIZE) <= total_mem);

donate_end:
	(void)sro_ctx_seal();
}

void smc_op_mem_reclaim(unsigned long handle,
			unsigned long list_addr,
			unsigned long list_count,
			struct smc_result *res)
{
	unsigned long list_offset;
	struct sro_context *sro;
	bool found;
	bool ret;

	/*
	 * The list can start at any place inside a given granule (provided
	 * that is aligned to 8 bytes).
	 *
	 * Calculate the offset of the first entry with regards to the start
	 * of the granule where the list is. We will use this to find out if
	 * we can cross granules when walking the list.
	 */
	list_offset = (list_addr & ~GRANULE_MASK) / sizeof(unsigned long);

	/*
	 * Limit the number of entries to not cross granules.
	 * The command will terminate with INCOMPLETE if there is a granule cross.
	 * Cap list_count before the addition to prevent integer overflow.
	 */
	list_count = MIN(list_count, ADDR_LIST_MAX_RANGES);
	list_count = (((list_count + list_offset) > ADDR_LIST_MAX_RANGES) ?
				(ADDR_LIST_MAX_RANGES - list_offset) : list_count);

	found = sro_ctx_find(handle);
	if (!found) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!ALIGNED(list_addr, sizeof(unsigned long))) {
		res->x[0] = RMI_ERROR_INPUT;
		goto reclaim_end;
	}

	sro = my_sro_ctx();

	if (sro->expected_fid != SMC_RMI_OP_MEM_RECLAIM) {
		res->x[0] = RMI_ERROR_INPUT;
		goto reclaim_end;
	}

	if (list_count == 0UL) {
		res->x[0] = (RMI_INCOMPLETE |
				INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_RECLAIM) |
				INPLACE(RMI_OP_CAN_CANCEL_BIT, SRO_CAN_CANCEL_FLAG(sro)));
		res->x[1] = 0UL;
		goto reclaim_end;
	}

	/*
	 * If the addr_list is empty or not of type RECLAIM, initialize it
	 * for a new reclaim operation. If the addr_list is not empty, it
	 * means that we have a pending reclaim operation with some entries
	 * that need to be copied. The type != OUTPUT check
	 * is when a DONATE call failure triggers a reclaim in the same SRO context, so we need
	 * to re-initialize the list for RECLAIM.
	 */
	if (addr_list_is_empty(&sro->addr_list) || (sro->addr_list.type != LIST_TYPE_OUTPUT)) {
		sro->range_desc_count = list_count;
		addr_list_init(&sro->addr_list, LIST_TYPE_OUTPUT);
		rmi_op_dispatch(SMC_RMI_OP_MEM_RECLAIM, res);
	}

	if (!addr_list_is_empty(&sro->addr_list)) {
		unsigned int copied = 0U;

		assert(unpack_return_code(sro->reclaim_res).status == RMI_INCOMPLETE);

		/*
		 * If the addr_list is not empty, it means that we have a
		 * pending reclaim operation with some entries that
		 * need to be processed. In case of error, we need to return
		 * back to the caller with OP_MEM_RECLAIM.
		 */
		sro->expected_fid = SMC_RMI_OP_MEM_RECLAIM;

		ret = addr_list_partial_copy_to_host(&sro->addr_list,
					list_addr, (unsigned int)list_count, &copied);
		if (!ret) {
			res->x[0] = RMI_ERROR_INPUT;
			res->x[1] = 0UL;
			goto reclaim_end;
		}

		if (addr_list_is_empty(&sro->addr_list)) {
			/* All pending entries have been processed, return the result */
			res->x[0] = sro->reclaim_res;
			res->x[1] = copied;
			sro->expected_fid = sro->prev_exp_fid;
		} else {
			/* Still pending entries, return INCOMPLETE */
			res->x[0] = (RMI_INCOMPLETE |
				INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_RECLAIM) |
				INPLACE(RMI_OP_CAN_CANCEL_BIT, SRO_CAN_CANCEL_FLAG(sro)));
			res->x[1] = copied;
		}
	}

reclaim_end:
	(void)sro_ctx_seal();

}

void smc_op_continue(unsigned long handle, unsigned long flags,
		struct smc_result *res)
{
	struct sro_context *sro;
	bool found;

	found = sro_ctx_find(handle);

	if (found == false) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);

	if (sro->expected_fid != SMC_RMI_OP_CONTINUE) {
		res->x[0] = RMI_ERROR_INPUT;
		(void)sro_ctx_seal();
		return;
	}

	sro->flags = flags;
	rmi_op_dispatch(SMC_RMI_OP_CONTINUE, res);

	if ((unpack_return_code(res->x[0]).status == RMI_INCOMPLETE) ||
	    (unpack_return_code(res->x[0]).status == RMI_BUSY)) {
		(void)sro_ctx_seal();
	} else {
		sro_ctx_release();
	}
}

void smc_op_cancel(unsigned long handle,
		struct smc_result *res)
{
	struct sro_context *sro;
	bool found;

	found = sro_ctx_find(handle);
	if (found == false) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);

	if (!sro->can_cancel) {
		res->x[0] = RMI_ERROR_INPUT;
		(void)sro_ctx_seal();
		return;
	}

	rmi_op_dispatch(SMC_RMI_OP_CANCEL, res);

	if ((unpack_return_code(res->x[0]).status == RMI_INCOMPLETE) ||
	    (unpack_return_code(res->x[0]).status == RMI_BUSY)) {
		(void)sro_ctx_seal();
	} else {
		sro_ctx_release();
	}
}

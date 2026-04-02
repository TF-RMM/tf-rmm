/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

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

/* Return the size requested by an entry on the RmiAddrRangeDesc4KB list */
static unsigned long calc_entry_size(unsigned long entry)
{
	int blk_size = (int)EXTRACT(RMI_ADDR_RDESC_4K_SZ, entry);

	/*
	 * The block size encoding coincides with the xlat level encoding for
	 * a block of the same size.
	 */
	blk_size = XLAT_TABLE_LEVEL_MAX - blk_size;
	return (XLAT_BLOCK_SIZE(blk_size) * EXTRACT(RMI_ADDR_RDESC_4K_CNT, entry));
}

/* Return the amount of memory requested in a donate operation */
static unsigned long calc_total_mem(const unsigned long *list, unsigned long count)
{
	unsigned long size = 0UL;

	assert(count > 0UL);

	for (unsigned long i = 0UL; i < count; i++) {
		size += calc_entry_size(list[i]);
	}

	return size;
}

/*
 * Copy a list of addresses from the SRO context to a buffer
 * in NS memory provided by the host.
 */
static bool copy_list_to_ns(unsigned long list_gr_ipa,
			unsigned long list_offset, void *src_buf,
			unsigned long list_count)
{
	struct granule *list_gr;

	list_gr = find_granule(list_gr_ipa);
	if ((list_gr == NULL) ||
		(granule_unlocked_state(list_gr) != GRANULE_STATE_NS)) {
		return false;
	}

	if (!ns_buffer_write(SLOT_NS, list_gr,
			     (unsigned int)(list_offset * sizeof(unsigned long)),
			     (list_count * sizeof(unsigned long)),
			     src_buf)) {
		return false;
	}

	return true;
}

static void rmi_op_dispatch(struct smc_args *args,
			    struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	unsigned long fid = args->v[0];
	unsigned long  handle_id;

	assert(sro != NULL);

	handle_id = RMI_HANDLER_ID(sro->init_command);
	assert(handle_id < ARRAY_SIZE(sro_handles));
	assert(sro_handles[handle_id].cb != NULL);

	if ((fid != SMC_RMI_OP_CANCEL) && (sro->expected_fid != fid)) {
		/*
		 * This is not the expected SRO RMI, so try again.
		 *
		 * In this case we can just return again the values for
		 * the previous command, just setting res->x[1] = 0
		 * as that value is used as 'donated_count' or
		 * 'reclaim_count' for donation or reclaim and we don't
		 * want the host to donate nor reclaim any memory.
		 */

		/* @TODO: Check this behavior against the spec */
		sro->prev_res.x[1] = 0UL;
		*res = sro->prev_res;
		return;
	}

	sro_handles[handle_id].cb(args, res);

	if (unpack_return_code(res->x[0]).status == RMI_INCOMPLETE) {
		unsigned long mem_op = EXTRACT(RMI_OP_MEM_REQ, res->x[0]);

		/* Update the memory flags on the SRO context if needed */
		sro->can_cancel = (EXTRACT(RMI_OP_CAN_CANCEL_BIT, res->x[0]) ==
								RMI_OP_CAN_CANCEL);

		if (mem_op == RMI_OP_MEM_REQ_DONATE) {
			unsigned long blk_size = EXTRACT(RMI_OP_DONATE_BLK_SIZE, res->x[2]);

			sro->transfer_req = ((XLAT_BLOCK_SIZE((int)(XLAT_TABLE_LEVEL_MAX - (int)blk_size))) *
						EXTRACT(RMI_OP_DONATE_BLK_COUNT, res->x[2]));
			sro->is_contig =
				(EXTRACT(RMI_OP_DONATE_MEM_CONTIG, res->x[2]) ==
							RMI_OP_MEM_CONTIG);
			sro->current_transfer = 0UL;
			/* TODO, store the state of memory and validate against incoming list */
		}

		if ((mem_op == RMI_OP_MEM_REQ_RECLAIM) ||
			((fid == SMC_RMI_OP_MEM_RECLAIM) &&
			(res->x[1] > 0UL))) {
			/*
			 * Reclaim cb result. Also handle the case where
			 * all entries fit in one batch (MEM_REQ_NONE) but
			 * still need to be copied to NS memory.
			 */
			sro->reclaim_res = res->x[0];
			sro->pend_entries = res->x[1];
			sro->prev_exp_fid = sro->expected_fid;
		} else {
			sro->prev_res = *res;
		}
	}
}

static void do_rmi_mem_op(unsigned long fid,
			  unsigned long handle,
			  unsigned long list_count,
			  struct smc_result *res)
{
	/*
	 * @TODO: Validate the following failure conditions for
	 * RMI_OP_MEM_DONATE.
	 *
	 * 	- complete
	 * 	- mem_state
	 */
	struct smc_args args;
	struct sro_context *sro;

	sro = my_sro_ctx();
	assert(sro != NULL);

	args.v[0] = fid;
	args.v[1] = handle;
	args.v[2] = (unsigned long)&(sro->list_buffer[0]);
	args.v[3] = list_count;
	rmi_op_dispatch(&args, res);
}

/*
 * Return the minimum alignment required by a RmiAddrRangeDesc4KB list.
 *
 * Each entry  in the list is an RMI address descriptor that encodes both
 * an address and a sized field.
 * The size field indicates how large a memory region that entry describes
 * (e.g. a 4KB page, a 2MB block or a 1GB block). The minimum alignment is
 * the biggest block size found across all entries. For instance, if one
 * entry describes a 2MB block and another describes a 4KB page, the minimum
 * alignment would be 2MB.
 */
static unsigned long min_alignment_req(const unsigned long *list, unsigned long count)
{
	unsigned long alignment = XLAT_BLOCK_SIZE(XLAT_TABLE_LEVEL_MAX);

	for (unsigned long i = 0UL; i < count; i++) {
		/*
		 * The block size encoding coincides with the xlat level encoding for
		 * a block of the same size.
		 */
		int blk_size = (int)EXTRACT(RMI_ADDR_RDESC_4K_SZ, list[i]);
		unsigned long new_alignment =
			XLAT_BLOCK_SIZE(XLAT_TABLE_LEVEL_MAX - blk_size);

		if (new_alignment > alignment) {
			/* Required alignment is larger than the current one */
			alignment = new_alignment;
		}
	}

	return alignment;
}

void smc_op_mem_donate(unsigned long handle,
			unsigned long list_addr,
			unsigned long list_count,
			struct smc_result *res)
{
	bool found;
	struct sro_context *sro;
	struct granule *list_gr;
	unsigned long entry_addr;
	unsigned long min_alignment;
	unsigned long list_offset;

	found = sro_ctx_find(handle);
	if (!found) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);

	if (!ALIGNED(list_addr, sizeof(unsigned long))) {
		res->x[0] = RMI_ERROR_INPUT;
		goto donate_end;
	}

	/*
	 * The list can start at any place inside a given granule (provided
	 * that is aligned to 8 bytes).
	 *
	 * Calculate the offset of the first entry with regards to the start
	 * of the granule where the list is.
	 */
	list_offset = (list_addr & ~GRANULE_MASK) >> 3UL;

	/*
	 * Limit the number of entries to not cross granules.
	 * The command will terminate with INCOMPLETE if there is a granule cross.
	 * Cap list_count before the addition to prevent integer overflow.
	 */
	list_count = MIN(list_count, SRO_MAX_LIST_ENTRIES);
	list_count = (((list_count + list_offset) > SRO_MAX_LIST_ENTRIES) ?
				(SRO_MAX_LIST_ENTRIES - list_offset) : list_count);

	if (sro->is_contig && (list_count > 1UL)) {
		/*
		 * If the memory is contiguous, the list should only have
		 * one entry.
		 */
		/*
		 * @TODO: Is this the right behavior or should we just ignore
		 * all but the first entry?
		 */
		res->x[0] = RMI_ERROR_INPUT;
		goto donate_end;
	}

	list_gr = find_granule(list_addr & GRANULE_MASK);
	if ((list_gr == NULL) || (granule_unlocked_state(list_gr) != GRANULE_STATE_NS)) {
		/* @TODO: Double check this fault cond is in the spec */
		res->x[0] = RMI_ERROR_INPUT;
		goto donate_end;
	}

	if (!ns_buffer_read(SLOT_NS, list_gr,
			    (unsigned int)(list_offset * sizeof(unsigned long)),
			    (list_count * sizeof(unsigned long)),
			    (void *)&(sro->list_buffer[0]))) {
		res->x[0] = RMI_ERROR_INPUT;
		goto donate_end;
	}

	sro->current_transfer = calc_total_mem(&(sro->list_buffer[0]), list_count);
	if (sro->current_transfer > sro->transfer_req) {
		res->x[0] = RMI_ERROR_INPUT;
		goto donate_end;
	}

	/*
	 * Enforce a uniform alignment constraint across all address entries
	 * in the donation list, ensuring they are all aligned to the largest
	 * block size described by any entry in the list.
	 */
	min_alignment = min_alignment_req(&(sro->list_buffer[0]), list_count);
	for (unsigned long i = 0UL; i < list_count; i++) {
		entry_addr = RMI_ADDR_RDESC_4K_GET_ADDR(sro->list_buffer[i]);

		if (!ALIGNED(entry_addr, min_alignment)) {
			res->x[0] = RMI_ERROR_INPUT;
			goto donate_end;
		}
	}

	do_rmi_mem_op(SMC_RMI_OP_MEM_DONATE, handle, list_count, res);
	assert(res->x[1] <= list_count);

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
	list_offset = (list_addr & ~GRANULE_MASK) >> 3UL;

	/*
	 * Limit the number of entries to not cross granules.
	 * The command will terminate with INCOMPLETE if there is a granule cross.
	 * Cap list_count before the addition to prevent integer overflow.
	 */
	list_count = MIN(list_count, SRO_MAX_LIST_ENTRIES);
	list_count = (((list_count + list_offset) > SRO_MAX_LIST_ENTRIES) ?
				(SRO_MAX_LIST_ENTRIES - list_offset) : list_count);

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

	if (sro->pend_entries == 0UL) {
		do_rmi_mem_op(SMC_RMI_OP_MEM_RECLAIM, handle,
			      list_count, res);
	}

	if (sro->pend_entries != 0UL) {
		assert(unpack_return_code(sro->reclaim_res).status == RMI_INCOMPLETE);

		/*
		 * If the pend_entries is not 0, it means that we have a
		 * pending reclaim operation with some entries that
		 * need to be processed. In case of error, we need to return
		 * back to the caller with OP_MEM_RECLAIM.
		 */
		sro->expected_fid = SMC_RMI_OP_MEM_RECLAIM;

		/*
		 * Cater for the case in which the host specified a count
		 * less than the pending entries.
		 */
		list_count = MIN(list_count, sro->pend_entries);

		ret = copy_list_to_ns(list_addr & GRANULE_MASK,
			 list_offset, (void *)&sro->list_buffer[0], list_count);
		if (!ret) {
			res->x[0] = RMI_ERROR_INPUT;
			res->x[1] = 0UL;
			goto reclaim_end;
		} else {
			sro->pend_entries -= list_count;
		}

		if (sro->pend_entries == 0UL) {
			/* All pending entries have been processed, return the result */
			res->x[0] = sro->reclaim_res;
			res->x[1] = list_count;
			sro->expected_fid = sro->prev_exp_fid;
		} else {
			/* Still pending entries, return INCOMPLETE */
			res->x[0] = (RMI_INCOMPLETE |
				INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_RECLAIM) |
				INPLACE(RMI_OP_CAN_CANCEL_BIT, SRO_CAN_CANCEL_FLAG(sro)));
			res->x[1] = list_count;

			/* Move the remaining pending entries to the start of the buffer */
			(void)memmove((void *)&(sro->list_buffer[0]),
			      (void *)&(sro->list_buffer[list_count]),
			      (size_t)sro->pend_entries * sizeof(unsigned long));
		}
	}

reclaim_end:
	(void)sro_ctx_seal();

}

void smc_op_continue(unsigned long flags,
		unsigned long handle,
		struct smc_result *res)
{
	struct smc_args args;
	struct sro_context *sro __unused;
	bool found;

	found = sro_ctx_find(handle);

	if (found == false) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);

	args.v[0] = SMC_RMI_OP_CONTINUE;
	args.v[1] = flags;
	args.v[2] = handle;
	rmi_op_dispatch(&args, res);

	if (unpack_return_code(res->x[0]).status == RMI_INCOMPLETE) {
		(void)sro_ctx_seal();
	} else {
		sro_ctx_release();
	}
}

void smc_op_cancel(unsigned long flags,
		unsigned long handle,
		struct smc_result *res)
{
	struct smc_args args;
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

	args.v[0] = SMC_RMI_OP_CANCEL;
	args.v[1] = flags;
	args.v[2] = handle;
	rmi_op_dispatch(&args, res);

	if (unpack_return_code(res->x[0]).status == RMI_INCOMPLETE) {
		(void)sro_ctx_seal();
	} else {
		sro_ctx_release();
	}
}

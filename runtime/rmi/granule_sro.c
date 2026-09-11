/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <buffer.h>
#include <dev_granule.h>
#include <granule.h>
#include <granule_sro.h>
#include <rmm_el3_gpi.h>
#include <rmm_el3_ifc.h>
#include <smc-rmi.h>
#include <smc.h>
#include <sro_context.h>
#include <status.h>
#include <stdbool.h>
#include <tracking_region.h>
#include <utils_def.h>

/* Encode a tracking mismatch at @addr for an RMI result. */
static unsigned long granule_tracking_error(unsigned long addr)
{
	return pack_return_code_level_addr(RMI_ERROR_TRACKING,
					   (unsigned char)0U, addr);
}

/* Return whether a stateless delegation response permits retrying the suffix. */
static bool granule_delegate_can_retry(int ret)
{
	return (ret == E_RMM_OK) || (ret == E_RMM_BUSY);
}

/*
 * Reserve an SRO context before asking EL3 to delegate a range.
 *
 * Reserving first guarantees that a cookie returned by FIRME can always be
 * retained. A synchronous response releases the unused context. An incomplete
 * response or a partial tracking unit leaves it reserved for the caller to
 * initialize and seal for continuation or rollback.
 *
 * @processed_size receives the prefix which remains delegated on return. If a
 * conflict or permanent EL3 failure stops within a tracking unit, the caller
 * must retain the granule in PARTIAL state and arrange rollback through
 * the SRO. Partial success or BUSY within a tracking unit instead retains the
 * context for a fresh GPI_SET. @el3 retains the shared continuation state.
 *
 * Return:
 *	- RMI_SUCCESS: A non-empty tracking-aligned prefix remains delegated.
 *	- RMI_INCOMPLETE: A stateful operation or stateless retry needs an SRO.
 *	- An encoded RMI_ERROR_TRACKING with level 0 and @addr: EL3 failed
 *	  permanently within a tracking unit. The context remains reserved for
 *	  rollback; this error must not reach the Host until rollback completes.
 *	- RMI_BUSY: EL3 is busy without progress, or no SRO context
 *		    is free and at least one is reserved.
 *	- RMI_BLOCKED: All SRO contexts are sealed, or EL3 reported a conflict.
 *	  A partial tracking unit retains its context for rollback; this result
 *	  must not reach the Host until that prefix has been returned to NS.
 *	- RMI_ERROR_INPUT: EL3 failed before making progress.
 */
static unsigned long granule_range_delegate_el3(unsigned long addr,
						unsigned long size,
						unsigned long tracking_size,
						unsigned long *processed_size,
						struct rmm_el3_gpi_state *el3)
{
	unsigned long reserve_ret;
	int el3_ret;

	assert((processed_size != NULL) && (el3 != NULL));
	*processed_size = 0UL;
	*el3 = (struct rmm_el3_gpi_state){0};

	/*
	 * Reserve only after the caller has selected an eligible range, so an
	 * invalid or already-delegated range does not consume an SRO context.
	 * Also any tracking size mismatches can be detected before reserving
	 * any SRO context, preventing unnecessary reservation of resources.
	 * Reserve before invoking EL3 so any returned cookie can be retained.
	 */
	reserve_ret = sro_ctx_reserve(SMC_RMI_GRANULE_RANGE_DELEGATE, 0UL,
				      false, false, SMC_RMI_OP_CONTINUE);
	if (reserve_ret != RMI_SUCCESS) {
		return reserve_ret;
	}

	el3_ret = rmm_el3_ifc_gtsi_step(addr, size, true, processed_size, el3);
	if (el3->incomplete) {
		return RMI_INCOMPLETE;
	}
	if ((*processed_size % tracking_size) != 0UL) {
		/*
		 * EL3 progress is Granule-aligned, so only coarse tracking can
		 * reach this branch. Retain the SRO for completion or rollback.
		 */
		if (granule_delegate_can_retry(el3_ret)) {
			return RMI_INCOMPLETE;
		}
		if (el3_ret == E_RMM_AGAIN) {
			return RMI_BLOCKED;
		}
		return granule_tracking_error(addr);
	}

	sro_ctx_release();
	/* A complete tracking-aligned prefix takes precedence over a suffix error. */
	if (*processed_size > 0UL) {
		return RMI_SUCCESS;
	}
	if (el3_ret == E_RMM_AGAIN) {
		/* Another operation must complete before this range can progress. */
		return RMI_BLOCKED;
	}
	if (el3_ret == E_RMM_BUSY) {
		return RMI_BUSY;
	}

	assert(el3_ret != E_RMM_OK);
	return RMI_ERROR_INPUT;
}

/*
 * Initialize the SRO state for a delegation which needs continuation or
 * rollback. @el3 retains the first EL3 response. A stateless retry leaves its
 * incomplete flag clear and @rollback_status as RMI_SUCCESS for a fresh
 * GPI_SET. Otherwise @rollback_status is the error to report after rollback.
 * @processed_size is the prefix already changed to Realm PAS; the remaining
 * granules, or the entire coarse granule, stay PARTIAL until completion.
 */
static void granule_delegate_ctx_init(unsigned long addr,
				      unsigned long size,
				      unsigned long tracking_size,
				      unsigned long processed_size,
				      const struct rmm_el3_gpi_state *el3,
				      bool device,
				      unsigned long rollback_status)
{
	struct sro_granule_delegate_ctx *ctx =
		&my_sro_ctx()->granule_delegate_ctx;

	assert((size > processed_size) && GRANULE_ALIGNED(processed_size));
	ctx->addr = addr;
	ctx->size = size;
	ctx->tracking_size = tracking_size;
	ctx->processed_size = processed_size;
	ctx->rollback_size = 0UL;
	ctx->el3 = *el3;
	ctx->device = device;
	ctx->rollback_status = rollback_status;
}

/*
 * Delegate one maximal run of conventional fine-tracked NS Granules.
 *
 * The Granule library stops the locked run before an already delegated or
 * otherwise ineligible granule, a bank boundary, the tracking-region top,
 * or @end_addr. Consequently, the EL3 range contains no Granule which was
 * already delegated when its granule was locked. A stateless FIRME partial
 * response commits only its processed prefix and returns that progress to the
 * Host. A stateful response reserves the remaining granules in PARTIAL
 * state and retains the cookie in an SRO context.
 *
 * Return RMI_SUCCESS after delegating a non-empty prefix or RMI_INCOMPLETE
 * after retaining a FIRME cookie. Return RMI_BUSY if EL3 is busy, or if no SRO
 * context is free and at least one is reserved. Return RMI_BLOCKED if all SRO
 * contexts are sealed or EL3 reports a conflict without progress. Return
 * another RMI error if the run could not be locked or EL3 otherwise failed
 * without making progress.
 */
static unsigned long granule_range_delegate_fine(unsigned long addr,
						  unsigned long end_addr,
						  unsigned long *progress)
{
	struct rmm_el3_gpi_state el3;
	unsigned long delegated_count;
	unsigned long locked_count;
	unsigned long processed_size;
	unsigned long request_size;
	unsigned long ret;

	ret = tr_find_lock_fine_granule_run(addr, end_addr,
						GRANULE_STATE_NS, &locked_count);
	if (ret != RMI_SUCCESS) {
		return ret;
	}

	request_size = locked_count * GRANULE_SIZE;

	ret = granule_range_delegate_el3(addr, request_size, GRANULE_SIZE,
					 &processed_size, &el3);

	assert((processed_size <= request_size) &&
	       GRANULE_ALIGNED(processed_size));

	delegated_count = processed_size / GRANULE_SIZE;
	granule_range_delegate_fine_unlock(addr, locked_count,
						   delegated_count,
						   ret == RMI_INCOMPLETE);

	if (ret == RMI_INCOMPLETE) {
		granule_delegate_ctx_init(addr, request_size, GRANULE_SIZE,
					 processed_size, &el3, false, RMI_SUCCESS);
		return ret;
	}

	assert(unpack_return_code(ret).status != RMI_ERROR_TRACKING);
	if (ret != RMI_SUCCESS) {
		return ret;
	}

	assert(delegated_count != 0UL);
	*progress = processed_size;
	return RMI_SUCCESS;
}

/*
 * Delegate one maximal run of device fine-tracked NS Granules.
 *
 * The locked run is homogeneous in coherency type and excludes granules
 * which were already delegated. Commit only the tracking-aligned EL3 prefix
 * and report that prefix as range progress. A stateful response reserves the
 * remaining granules in PARTIAL state and retains its cookie in an SRO
 * context.
 *
 * Return RMI_SUCCESS after delegating a non-empty prefix or RMI_INCOMPLETE
 * after retaining a FIRME cookie. Return RMI_BUSY if EL3 is busy, or if no SRO
 * context is free and at least one is reserved. Return RMI_BLOCKED if all SRO
 * contexts are sealed or EL3 reports a conflict without progress. Return
 * another RMI error if the run could not be locked or EL3 otherwise failed
 * without making progress.
 */
static unsigned long granule_range_delegate_fine_dev(
						unsigned long addr,
						unsigned long end_addr,
						unsigned long *progress)
{
	enum dev_coh_type type __unused;
	struct rmm_el3_gpi_state el3;
	unsigned long delegated_count;
	unsigned long locked_count;
	unsigned long processed_size;
	unsigned long request_size;
	unsigned long ret;

	ret = tr_find_lock_fine_dev_granule_run(
					addr, end_addr, DEV_GRANULE_STATE_NS,
					&type, &locked_count);
	if (ret != RMI_SUCCESS) {
		return ret;
	}

	request_size = locked_count * GRANULE_SIZE;
	ret = granule_range_delegate_el3(addr, request_size, GRANULE_SIZE,
					 &processed_size, &el3);
	assert((processed_size <= request_size) &&
	       GRANULE_ALIGNED(processed_size));
	delegated_count = processed_size / GRANULE_SIZE;
	granule_range_delegate_fine_dev_unlock(addr, locked_count,
						       delegated_count,
						       ret == RMI_INCOMPLETE);

	if (ret == RMI_INCOMPLETE) {
		granule_delegate_ctx_init(addr, request_size, GRANULE_SIZE,
					 processed_size, &el3, true, RMI_SUCCESS);
		return ret;
	}

	assert(unpack_return_code(ret).status != RMI_ERROR_TRACKING);
	if (ret != RMI_SUCCESS) {
		return ret;
	}

	assert(delegated_count != 0UL);
	*progress = processed_size;
	return RMI_SUCCESS;
}

/*
 * Return whether a complete, aligned tracking unit fits at the start of
 * the remaining range.
 */
static bool granule_range_tracking_fits(unsigned long addr,
					unsigned long end_addr,
					unsigned long tracking_size)
{
	return ALIGNED(addr, tracking_size) &&
	       ((end_addr - addr) >= tracking_size);
}

/*
 * Delegate one complete coarse tracking region through EL3.
 *
 * The caller must hold the granule lock for the region. This function does
 * not release that lock or update the granule state. Partial progress is
 * retained in an SRO context for suffix retry, rollback or continuation; the
 * caller changes the granule to PARTIAL until the SRO completes.
 *
 * Return RMI_SUCCESS if EL3 delegated the complete region or RMI_INCOMPLETE if
 * continuation, suffix retry or rollback is needed. Return RMI_BUSY if EL3 is
 * busy, or if no SRO context is free and at least one is reserved. Return
 * RMI_BLOCKED if all SRO contexts are sealed or EL3 conflicts without progress.
 * Return RMI_ERROR_INPUT for a permanent failure before any progress. Rollback
 * reports RMI_BLOCKED for a conflict or RMI_ERROR_TRACKING for a permanent
 * failure, only after the delegated prefix has been returned to NS.
 */
static unsigned long granule_range_delegate_coarse(
						unsigned long addr,
						unsigned long tracking_size,
						bool device)
{
	struct rmm_el3_gpi_state el3;
	unsigned long processed_size;
	unsigned long ret;
	bool rollback;

	assert((tracking_size > GRANULE_SIZE) &&
	       ALIGNED(addr, tracking_size));

	ret = granule_range_delegate_el3(addr, tracking_size, tracking_size,
					 &processed_size, &el3);
	assert(processed_size <= tracking_size);
	/*
	 * Coarse tracking cannot represent a partially delegated region. Roll back
	 * a non-empty prefix before reporting a conflict or permanent failure.
	 * With zero progress, there is nothing to undo; RMI_BLOCKED may also mean
	 * that no SRO context could be reserved.
	 */
	rollback = (processed_size != 0UL) &&
		   ((ret == RMI_BLOCKED) ||
		    (unpack_return_code(ret).status == RMI_ERROR_TRACKING));
	if ((ret == RMI_INCOMPLETE) || rollback) {
		granule_delegate_ctx_init(addr, tracking_size, tracking_size,
					 processed_size, &el3, device,
					 rollback ? ret : RMI_SUCCESS);
		return RMI_INCOMPLETE;
	}
	if (ret != RMI_SUCCESS) {
		return ret;
	}

	assert(processed_size == tracking_size);
	return RMI_SUCCESS;
}

/*
 * Delegate or skip a device tracking range beginning at @addr.
 *
 * Fine tracking delegates the maximal eligible granule run. Coarse
 * tracking keeps its granule locked across the EL3 call, then marks it
 * DELEGATED on completion or PARTIAL while an SRO handles unfinished work.
 * No lock is held on return.
 *
 * Return RMI_SUCCESS and set @progress for a delegated or already-delegated
 * range. @already_delegated is true only when the range was already in the
 * target state and no EL3 call was made. Return RMI_INCOMPLETE when an SRO
 * retains progress for FIRME continuation, stateless suffix retry or coarse
 * rollback. Granules with pending work remain PARTIAL. Otherwise, return
 * the RMI error describing why no progress was made.
 */
static unsigned long granule_range_delegate_device(unsigned long addr,
						     unsigned long end_addr,
						     unsigned long *progress,
						     bool *already_delegated)
{
	struct dev_granule *g;
	unsigned long tracking_size;
	unsigned long ret;
	bool in_target;

	assert((progress != NULL) && (already_delegated != NULL));
	*already_delegated = false;

	ret = granule_range_lock_device(addr, DEV_GRANULE_STATE_NS,
					 DEV_GRANULE_STATE_DELEGATED, &g,
					 &tracking_size, &in_target);
	if (ret != RMI_SUCCESS) {
		return ret;
	}

	if (!granule_range_tracking_fits(addr, end_addr, tracking_size)) {
		dev_granule_unlock(g);
		return granule_tracking_error(addr);
	}

	if (in_target) {
		dev_granule_unlock(g);
		*progress = tracking_size;
		*already_delegated = true;
		return RMI_SUCCESS;
	}

	if (tracking_size == GRANULE_SIZE) {
		dev_granule_unlock(g);
		return granule_range_delegate_fine_dev(addr, end_addr,
							progress);
	}

	ret = granule_range_delegate_coarse(addr, tracking_size, true);
	if (ret == RMI_SUCCESS) {
		dev_granule_unlock_transition(g, DEV_GRANULE_STATE_DELEGATED);
		*progress = tracking_size;
	} else if (ret == RMI_INCOMPLETE) {
		dev_granule_unlock_transition(g, DEV_GRANULE_STATE_PARTIAL);
	} else {
		dev_granule_unlock(g);
	}
	return ret;
}

/*
 * Delegate or skip a conventional or device tracking range beginning at
 * @addr.
 *
 * A conventional lookup returning RMI_ERROR_INPUT permits a device lookup at
 * the same address. Fine tracking delegates the maximal eligible granule
 * run. Coarse tracking keeps its granule locked across the EL3 call, then
 * marks it DELEGATED on completion or PARTIAL while an SRO handles unfinished
 * work. No lock is held on return.
 *
 * Return RMI_SUCCESS and set @progress for a delegated or already-delegated
 * range. @already_delegated is true only when the range was already in the
 * target state and no EL3 call was made. Return RMI_INCOMPLETE when an SRO
 * retains progress for FIRME continuation, stateless suffix retry or coarse
 * rollback. Granules with pending work remain PARTIAL. Otherwise, return
 * the RMI error describing why no progress was made.
 */
static unsigned long granule_range_delegate_one(unsigned long addr,
						 unsigned long end_addr,
						 unsigned long *progress,
						 bool *already_delegated)
{
	struct granule *g;
	unsigned long tracking_size;
	unsigned long ret;
	bool in_target;

	assert((progress != NULL) && (already_delegated != NULL));
	*already_delegated = false;

	ret = granule_range_lock_conventional(addr, GRANULE_STATE_NS,
					       GRANULE_STATE_DELEGATED, &g,
					       &tracking_size, &in_target);
	if (ret == RMI_ERROR_INPUT) {
		return granule_range_delegate_device(addr, end_addr, progress,
							    already_delegated);
	}
	if (ret != RMI_SUCCESS) {
		return ret;
	}
	if (!granule_range_tracking_fits(addr, end_addr, tracking_size)) {
		granule_unlock(g);
		return granule_tracking_error(addr);
	}
	if (in_target) {
		granule_unlock(g);
		*progress = tracking_size;
		*already_delegated = true;
		return RMI_SUCCESS;
	}
	if (tracking_size == GRANULE_SIZE) {
		granule_unlock(g);
		return granule_range_delegate_fine(addr, end_addr, progress);
	}

	ret = granule_range_delegate_coarse(addr, tracking_size, false);
	if (ret == RMI_SUCCESS) {
		granule_unlock_transition(g, GRANULE_STATE_DELEGATED);
		*progress = tracking_size;
	} else if (ret == RMI_INCOMPLETE) {
		granule_unlock_transition(g, GRANULE_STATE_PARTIAL);
	} else {
		granule_unlock(g);
	}
	return ret;
}

/* Return an SRO response which asks the Host to invoke RMI_OP_CONTINUE. */
static void granule_delegate_yield(struct smc_result *res)
{
	assert(res != NULL);
	res->x[0] = pack_return_code_incomplete(
			RMI_OP_MEM_REQ_NONE, RMI_OP_CANNOT_CANCEL);
	res->x[1] = 0UL;
	res->x[2] = 0UL;
}

/*
 * Resume the Realm transition phase of a range delegation.
 *
 * FIRME reports progress for this invocation only. Fine granules can
 * publish each completed Granule immediately. A coarse granule stays
 * PARTIAL until the entire tracking region is delegated. Stateless partial
 * success and BUSY yield before retrying a coarse suffix with GPI_SET.
 * A conflict or permanent failure rolls back a partially delegated coarse
 * region before reporting RMI_BLOCKED or RMI_ERROR_TRACKING respectively.
 * Fine progress instead completes the SRO once EL3 releases its stateful
 * operation, even on a suffix error. A conflict without accumulated progress
 * restores the source granules and returns RMI_BLOCKED immediately.
 * INCOMPLETE and continuation BUSY retain the operation and returned cookie;
 * BUSY adds no progress. All other responses invalidate the saved cookie.
 */
static void granule_delegate_resume_realm(
				struct sro_granule_delegate_ctx *ctx,
				struct smc_result *res)
{
	unsigned long processed_size;
	unsigned long progress;
	unsigned long remaining;
	int ret;

	assert((ctx != NULL) && (ctx->rollback_status == RMI_SUCCESS));
	processed_size = ctx->processed_size;
	ret = rmm_el3_ifc_gtsi_step(ctx->addr, ctx->size, true,
				  &processed_size, &ctx->el3);
	progress = processed_size - ctx->processed_size;

	/*
	 * Publish the newly completed fine-granule prefix before advancing the
	 * progress cursor. A coarse granule covers the whole tracking region
	 * and must remain PARTIAL until every Granule has reached Realm PAS.
	 */
	if ((ctx->tracking_size == GRANULE_SIZE) && (progress > 0UL)) {
		granule_delegate_fine_transition(
				ctx->addr + ctx->processed_size, progress, ctx->device, true);
	}
	ctx->processed_size += progress;

	if (ctx->el3.incomplete) {
		granule_delegate_yield(res);
		return;
	}
	/*
	 * Coarse progress must reach the region boundary before being reported.
	 * Fine progress can complete now; retry contention only if neither EL3
	 * nor the already-delegated prefix has advanced the original Host cursor.
	 */
	if (granule_delegate_can_retry(ret) &&
	    (ctx->processed_size < ctx->size) &&
	    ((ctx->tracking_size > GRANULE_SIZE) ||
	     ((ctx->processed_size == 0UL) && (ctx->addr == ctx->host_addr)))) {
		granule_delegate_yield(res);
		return;
	}

	/*
	 * A terminal EL3 response can leave part of a fine-tracked request
	 * unprocessed. The processed prefix was published as DELEGATED above;
	 * restore the remaining granules from PARTIAL to NS so their states
	 * continue to describe their PAS.
	 *
	 * Report progress relative to the original Host cursor. This includes any
	 * leading DELEGATED granules skipped before the EL3 request, as well as
	 * the prefix processed by EL3. If neither advanced the cursor, report the
	 * terminal failure at the original address.
	 */
	if (ctx->tracking_size == GRANULE_SIZE) {
		remaining = ctx->size - ctx->processed_size;
		if (remaining > 0UL) {
			granule_delegate_fine_transition(
				ctx->addr + ctx->processed_size, remaining,
				ctx->device, false);
		}
		if ((ctx->addr + ctx->processed_size) > ctx->host_addr) {
			res->x[0] = RMI_SUCCESS;
			res->x[1] = ctx->addr + ctx->processed_size;
		} else {
			res->x[0] = (ret == E_RMM_AGAIN) ? RMI_BLOCKED : RMI_ERROR_INPUT;
			res->x[1] = ctx->host_addr;
		}
		return;
	}

	/*
	 * Fine tracking has returned above. Publish the coarse granule as
	 * DELEGATED only after its entire tracking region is in Realm PAS.
	 */
	if (ctx->processed_size == ctx->size) {
		granule_delegate_coarse_transition(ctx->addr, ctx->tracking_size,
						  ctx->device, true);
		res->x[0] = RMI_SUCCESS;
		res->x[1] = ctx->addr + ctx->size;
		return;
	}
	if (ctx->processed_size == 0UL) {
		granule_delegate_coarse_transition(ctx->addr, ctx->tracking_size,
						  ctx->device, false);
		res->x[0] = (ret == E_RMM_AGAIN) ? RMI_BLOCKED : RMI_ERROR_INPUT;
		res->x[1] = ctx->host_addr;
		return;
	}

	/*
	 * A conflict or permanent error left a prefix which the coarse granule
	 * cannot represent as delegated.
	 * Keep it in PARTIAL state and yield before returning the delegated prefix
	 * to NS through the rollback phase. The granule is restored to NS only
	 * after that rollback completes.
	 */
	ctx->rollback_status = (ret == E_RMM_AGAIN) ? RMI_BLOCKED :
						granule_tracking_error(ctx->addr);
	granule_delegate_yield(res);
}

/*
 * Return a partially delegated coarse tracking region to Non-secure PAS.
 * Stateless rollback progress is restarted with GPI_SET; cookie-bearing
 * progress is resumed with GPI_OP_CONTINUE. Busy responses yield while the
 * granule stays PARTIAL. Undelegation cannot conflict because the SRO owns
 * the prefix. Only a completed rollback restores the granule to NS and
 * reports the saved RMI_BLOCKED or RMI_ERROR_TRACKING status to the Host.
 */
static void granule_delegate_resume_rollback(
				struct sro_granule_delegate_ctx *ctx,
				struct smc_result *res)
{
	unsigned long previous_size;
	unsigned long progress;
	int ret;

	assert((ctx != NULL) && (ctx->rollback_status != RMI_SUCCESS) &&
	       (ctx->rollback_size < ctx->processed_size));

	previous_size = ctx->rollback_size;
	ret = rmm_el3_ifc_gtsi_step(ctx->addr, ctx->processed_size, false,
				  &ctx->rollback_size, &ctx->el3);
	progress = ctx->rollback_size - previous_size;
	if (ctx->el3.incomplete) {
		granule_delegate_yield(res);
		return;
	}

	if ((ret == E_RMM_BUSY) && (progress == 0UL)) {
		granule_delegate_yield(res);
		return;
	}

	assert((ret == E_RMM_OK) && (progress > 0UL));

	if (ctx->rollback_size < ctx->processed_size) {
		granule_delegate_yield(res);
		return;
	}

	granule_delegate_coarse_transition(ctx->addr, ctx->tracking_size,
						  ctx->device, false);
	res->x[0] = ctx->rollback_status;
	res->x[1] = ctx->host_addr;
}

/*
 * Continue a pending range delegation or its coarse rollback, using GPI_SET
 * for a stateless suffix and GPI_OP_CONTINUE while a cookie remains valid.
 * The generic SRO dispatcher seals the context again for RMI_INCOMPLETE and
 * releases it after a terminal RMI result.
 */
void granule_delegate_continue(unsigned long fid,
			       struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	struct sro_granule_delegate_ctx *ctx;

	assert((sro != NULL) && (fid == SMC_RMI_OP_CONTINUE));
	assert(sro->init_command == SMC_RMI_GRANULE_RANGE_DELEGATE);
	(void)fid;
	ctx = &sro->granule_delegate_ctx;

	if (ctx->rollback_status != RMI_SUCCESS) {
		granule_delegate_resume_rollback(ctx, res);
	} else {
		granule_delegate_resume_realm(ctx, res);
	}
}

/*
 * Begin delegation or skip a contiguous prefix of the tracking region containing
 * @addr. @addr and @end_addr must be Granule aligned with @end_addr > @addr.
 * The caller must hold no Granule lock and initialize @res->x[0] to
 * RMI_ERROR_INPUT and @res->x[1] to @addr. Coarse tracking processes its single
 * granule atomically. Fine tracking skips any leading delegated Granules,
 * then issues at most one EL3 request for a contiguous range of NS Granules.
 * Progress never crosses the current tracking-region boundary; the Host must
 * reinvoke the command at the returned address to continue into the next region.
 * An error at the initial address is returned directly. After a delegated
 * prefix has been skipped, that prefix is returned as progress and the Host
 * observes an error at the next address on a subsequent invocation. If FIRME
 * retains an incomplete operation, return an SRO handle which the Host passes
 * to RMI_OP_CONTINUE.
 */
void granule_delegate_start(unsigned long addr,
				unsigned long end_addr,
				struct smc_result *res)
{
	unsigned long cursor;
	unsigned long progress;
	unsigned long region_remaining;
	unsigned long region_size;
	unsigned long region_top;
	unsigned long ret;
	bool already_delegated;

	/*
	 * Limit this invocation to one tracking region, so coarse tracking
	 * processes at most one coarse granule.
	 */
	region_size = tracking_region_get_size();
	region_remaining = region_size - (addr & (region_size - 1UL));
	region_top = end_addr;
	if ((end_addr - addr) > region_remaining) {
		/* The comparison ensures this addition cannot overflow. */
		region_top = addr + region_remaining;
	}
	cursor = addr;

	do {
		progress = 0UL;
		ret = granule_range_delegate_one(cursor, region_top, &progress,
							 &already_delegated);
		if (ret == RMI_INCOMPLETE) {
			struct sro_granule_delegate_ctx *ctx =
				&my_sro_ctx()->granule_delegate_ctx;

			ctx->host_addr = addr;
			res->x[0] = pack_return_code_incomplete(
					RMI_OP_MEM_REQ_NONE, RMI_OP_CANNOT_CANCEL);
			res->x[1] = (unsigned long)sro_ctx_seal();
			res->x[2] = 0UL;
			return;
		}
		if (ret != RMI_SUCCESS) {
			if (cursor == addr) {
				res->x[0] = ret;
				return;
			}

			/*
			 * Preserve the already-skipped prefix. The Host will retry
			 * @cursor and observe this error on its next invocation.
			 */
			break;
		}

		assert((progress > 0UL) && (progress <= (region_top - cursor)));
		cursor += progress;
	} while (already_delegated && (cursor < region_top));

	res->x[0] = RMI_SUCCESS;
	res->x[1] = cursor;
}

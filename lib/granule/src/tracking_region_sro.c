/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <granule.h>
#include <rmm_el3_gpi.h>
#include <rmm_el3_ifc.h>
#include <smc-rmi.h>
#include <smc.h>
#include <sro_context.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
/* coverity[unnecessary_header:SUPPRESS] */
#include <string.h>
#include <tracking_region_lock.h>
#include <tracking_region_pvt.h>
#include <utils_def.h>

#define TRACKING_SRO_CONV_ARRAY	U(1)
#define TRACKING_SRO_DEV_ARRAY	U(2)

/*
 * Explicit int casts convert these named selectors to the context fields'
 * MISRA essential type. Retain them with targeted clang-tidy annotations:
 * C enumeration constants already have type int.
 */

/* The tracking operation which owns the SRO context. */
enum tracking_sro_operation {
	/* A transition to FINE tracking which donates fine-granule backing. */
	TRACKING_SRO_SET_DONATE,
	/* A transition from FINE tracking which returns fine-granule backing. */
	TRACKING_SRO_SET_RECLAIM
};

/* The next callback to execute for a tracking SRO context. */
enum tracking_sro_callback {
	/* Receive and map a batch of Host-donated backing pages. */
	TRACKING_SRO_DONATE,
	/* Finish an EL3 delegation before mapping an accepted metadata page. */
	TRACKING_SRO_DELEGATE_CONTINUE,
	/* Complete the transition after all donated pages arrive. */
	TRACKING_SRO_CONTINUE,
	/* Return a batch of fine-granule backing pages to the Host. */
	TRACKING_SRO_RECLAIM,
	/* Complete reclaim and release the tracking-region transition marker. */
	TRACKING_SRO_FINISH
};

/*
 * Identify the fine-granule backing ranges that require donation before
 * tracking region @tr_idx can enter fine tracking.
 *
 * Select every conventional or device fine range in the region. Its metadata
 * VA must be unmapped: any previous fine backing was reclaimed before the
 * preceding transition completed.
 * Set the corresponding bit in @array_mask for every selected range and return
 * the nonzero total number of pages that the Host must donate. The caller must
 * own the transition marker for @tr.
 */
static unsigned long tracking_region_fine_donation_setup(
						struct tracking_region *tr,
						unsigned long tr_idx,
						unsigned int *array_mask)
{
	uintptr_t base = 0UL;
	unsigned long pages;
	unsigned long count = 0UL;

	assert((tr != NULL) && tracking_region_transition_pending(tr));
	assert(array_mask != NULL);
	(void)tr;
	*array_mask = 0U;
	if (tracking_region_fine_page_range(tr_idx, TR_MEM_TYPE_CONV,
					    &base, &pages)) {
		assert(!tracking_region_page_is_mapped(base));
		*array_mask |= TRACKING_SRO_CONV_ARRAY;
		count += pages;
	}
	if (tracking_region_fine_page_range(tr_idx, TR_MEM_TYPE_DEV,
					    &base, &pages)) {
		assert(!tracking_region_page_is_mapped(base));
		*array_mask |= TRACKING_SRO_DEV_ARRAY;
		count += pages;
	}

	assert(count != 0UL);
	return count;
}

/*
 * Identify the fine-granule backing ranges to reclaim when tracking region
 * @tr_idx leaves fine tracking.
 *
 * Set the corresponding bit in @array_mask for each conventional or device
 * range present in the region. Every selected range must already be mapped.
 * Return the nonzero total number of backing pages across the selected ranges.
 * The caller must own the transition marker for @tr.
 */
static unsigned long tracking_region_fine_reclaim_setup(
						struct tracking_region *tr,
						unsigned long tr_idx,
						unsigned int *array_mask)
{
	const enum tr_mem_type types[] = {
		TR_MEM_TYPE_CONV,
		TR_MEM_TYPE_DEV
	};
	const unsigned int masks[] = {
		TRACKING_SRO_CONV_ARRAY,
		TRACKING_SRO_DEV_ARRAY
	};
	unsigned long count = 0UL;

	assert((tr != NULL) && tracking_region_transition_pending(tr));
	assert(array_mask != NULL);
	(void)tr;
	*array_mask = 0U;
	for (unsigned int i = 0U; i < ARRAY_SIZE(types); i++) {
		uintptr_t base;
		unsigned long pages;

		if (!tracking_region_fine_page_range(tr_idx, types[i],
						     &base, &pages)) {
			continue;
		}
		assert(tracking_region_page_is_mapped(base));
		*array_mask |= masks[i];
		count += pages;
	}

	assert(count != 0UL);
	return count;
}

/*
 * Translate logical page @page_idx in a tracking SRO to its reserved metadata
 * VA.
 *
 * @page_idx must be within @ctx's requested transfer. SET_TRACKING uses one
 * logical index space for its conventional and device arrays even though
 * their VA ranges are separate and need not be adjacent. If the conventional
 * range contains N pages, indices [0, N) map into that range; subsequent
 * indices subtract N and map from the device range's VA base.
 *
 * Return the reserved VA for @page_idx; it need not yet have backing memory.
 */
static uintptr_t tracking_sro_page_va(const struct sro_tracking_ctx *ctx,
				      unsigned long page_idx)
{
	uintptr_t base = 0UL;
	unsigned long pages;
	bool found;

	assert((ctx != NULL) && (page_idx < ctx->requested_pages));

	if (((ctx->array_mask & TRACKING_SRO_CONV_ARRAY) != 0U) &&
	    tracking_region_fine_page_range(ctx->tr_idx, TR_MEM_TYPE_CONV,
					    &base, &pages)) {
		if (page_idx < pages) {
			return base + (page_idx * GRANULE_SIZE);
		}
		page_idx -= pages;
	}

	assert((ctx->array_mask & TRACKING_SRO_DEV_ARRAY) != 0U);
	found = tracking_region_fine_page_range(ctx->tr_idx, TR_MEM_TYPE_DEV,
						&base, &pages);
	assert(found);
	(void)found;
	assert(page_idx < pages);
	return base + (page_idx * GRANULE_SIZE);
}

/* Return whether @pa is self-describing metadata for the SET target. */
static bool tracking_sro_page_is_self_describing(
					const struct sro_tracking_ctx *ctx,
					uintptr_t pa)
{
	return (pa >= ctx->addr) &&
	       (pa < (ctx->addr + tracking_region_get_size()));
}

/* Return whether @pa belongs to a conventional-memory bank. */
static bool tracking_sro_page_is_conventional(uintptr_t pa)
{
	return tracking_region_find(pa, TR_MEM_TYPE_CONV) != NULL;
}

/*
 * Determine the RMI memory state of self-describing tracking metadata.
 *
 * The SRO must own the target region's transition marker. An untracked region
 * requires UNDELEGATED memory. For a coarse region, the claim acquired and
 * validated its granule before setting the marker. Translate NS or DELEGATED
 * to the corresponding RMI memory state. The marker prevents a new granule user
 * from changing that state after it is observed.
 *
 * Return true and write the state to @state when the current representation
 * permits self-describing metadata. Return false for any other Granule state.
 */
static bool tracking_sro_self_describing_state(
					const struct sro_tracking_ctx *ctx,
					unsigned long *state)
{
	struct tracking_region *tr = NULL;
	enum tr_state tracking_state;
	unsigned long tr_idx __unused;
	unsigned char granule_state;
	bool found __unused;
	bool valid = true;

	assert((ctx != NULL) && (state != NULL));
	found = tracking_region_set_tracking_find(ctx->addr, ctx->category,
						  &tr_idx, &tr);
	assert(found && (tr_idx == ctx->tr_idx));

	/* Stabilize the source representation while selecting its granule. */
	tracking_region_read_lock(tr);
	assert(tracking_region_transition_pending(tr));
	tracking_state = tracking_region_get_state(tr);
	if (tracking_state == trs_none) {
		*state = RMI_OP_MEM_UNDELEGATED;
	} else if (tracking_state == trs_coarse) {
		/*
		 * The claim completed all earlier granule users before setting
		 * the marker. Lock the SRO-owned granule while reading its state;
		 * ordinary lookups cannot acquire it while the marker is set.
		 */
		granule_bitlock_acquire(&tr->coarse_granule);
		granule_state = granule_get_state(&tr->coarse_granule);
		if (granule_state == GRANULE_STATE_NS) {
			*state = RMI_OP_MEM_UNDELEGATED;
		} else if (granule_state == GRANULE_STATE_DELEGATED) {
			*state = RMI_OP_MEM_DELEGATED;
		} else {
			valid = false;
		}
		granule_unlock(&tr->coarse_granule);
	} else {
		valid = false;
	}
	tracking_region_read_unlock(tr);

	return valid;
}

/*
 * Start or resume the current metadata page's PAS transition. The caller owns
 * the tracking SRO and retains @pa until the shared EL3 helper completes it.
 * @delegate selects Realm PAS. Return the EL3 status, retaining progress and
 * any continuation cookie; the caller clears gpi.pending after disposing of
 * the page or returning it to the Host for a stateless donation retry.
 */
static int tracking_sro_gpi_step(struct sro_tracking_ctx *ctx, uintptr_t pa,
				 bool delegate)
{
	assert((ctx != NULL) && GRANULE_ALIGNED(pa));
	if (!ctx->gpi.pending) {
		ctx->gpi = (struct sro_tracking_gpi_ctx){
			.pa = pa,
			.pending = true
		};
	}
	assert(ctx->gpi.pa == pa);
	return rmm_el3_ifc_gtsi_step(pa, GRANULE_SIZE, delegate,
				  &ctx->gpi.processed_size, &ctx->gpi.el3);
}

/*
 * Accept one UNDELEGATED donor after starting its Realm PAS transition.
 * Return RMI_SUCCESS for a completed or stateful delegation. A stateful operation
 * consumes the donor but leaves it unmapped until continuation completes.
 * Return RMI_BUSY for stateless contention so the Host can resubmit the page,
 * RMI_BLOCKED for an EL3 conflict, or RMI_ERROR_INPUT for other failures.
 */
static unsigned long tracking_sro_delegate_page(struct sro_tracking_ctx *ctx,
						uintptr_t pa)
{
	int ret = tracking_sro_gpi_step(ctx, pa, true);

	if (ctx->gpi.el3.incomplete) {
		return RMI_SUCCESS;
	}
	ctx->gpi.pending = false;
	if (ctx->gpi.processed_size == GRANULE_SIZE) {
		return RMI_SUCCESS;
	}
	if (ret == E_RMM_BUSY) {
		return RMI_BUSY;
	}
	return (ret == E_RMM_AGAIN) ? RMI_BLOCKED : RMI_ERROR_INPUT;
}

/*
 * Validate and claim one donated fine-metadata page.
 *
 * A non-self-describing page must be delegated conventional memory. A
 * self-describing page must be UNDELEGATED for NONE-to-FINE, or match the
 * coarse granule for COARSE-to-FINE. Claim an UNDELEGATED self-describing page
 * directly through EL3 because its fine granule does not exist yet.
 * Return RMI_SUCCESS when the page is claimed, or RMI_ERROR_INPUT when its
 * type, state or delegation is invalid. An incomplete EL3 delegation retains
 * the accepted page for continuation before mapping. Return RMI_BUSY for a
 * stateless EL3 retry, or RMI_BLOCKED for a conflict requiring donation rollback.
 */
static unsigned long tracking_sro_claim_fine_page(struct sro_tracking_ctx *ctx,
						  uintptr_t pa,
						  unsigned long state)
{
	if (tracking_sro_page_is_self_describing(ctx, pa)) {
		unsigned long expected_state;

		/*
		 * Claim the page through the shared EL3 helper because
		 * its target fine granule cannot represent the page until this
		 * donation installs the granule array. Tracking metadata must
		 * reside in DRAM.
		 */
		if (!tracking_sro_page_is_conventional(pa)) {
			return RMI_ERROR_INPUT;
		}
		if (!tracking_sro_self_describing_state(ctx, &expected_state) ||
		    (state != expected_state)) {
			return RMI_ERROR_INPUT;
		}
		if (state == RMI_OP_MEM_UNDELEGATED) {
			return tracking_sro_delegate_page(ctx, pa);
		}
		return RMI_SUCCESS;
	}

	/* The RMI specification requires non-self-describing pages to be delegated. */
	if (state == RMI_OP_MEM_DELEGATED) {
		struct granule *g;

		if (tr_find_lock_granule(pa, GRANULE_SIZE,
					GRANULE_STATE_DELEGATED,
					&g) == RMI_SUCCESS) {
			granule_unlock_transition(g, GRANULE_STATE_INTERNAL);
			return RMI_SUCCESS;
		}
	}

	return RMI_ERROR_INPUT;
}

/*
 * Claim one donated page at its logical SRO position. Map it only after its
 * PAS transition completes. Return RMI_SUCCESS for an accepted page, including
 * one retained for EL3 continuation. Otherwise propagate the claim status:
 * RMI_BUSY leaves the page available for another donation attempt; RMI_BLOCKED
 * or RMI_ERROR_INPUT requires reclaiming earlier accepted pages.
 */
static unsigned long tracking_sro_page_add(struct sro_tracking_ctx *ctx,
					   uintptr_t pa,
					   unsigned long state)
{
	uintptr_t va;
	unsigned long ret;

	assert((ctx != NULL) && GRANULE_ALIGNED(pa));
	ret = tracking_sro_claim_fine_page(ctx, pa, state);
	if (ret != RMI_SUCCESS) {
		return ret;
	}

	if (!ctx->gpi.pending) {
		int map_ret __unused;

		va = tracking_sro_page_va(ctx, ctx->transferred_pages);
		map_ret = tracking_region_page_populate(va, pa);
		assert(map_ret == 0);
	}

	ctx->transferred_pages++;
	return RMI_SUCCESS;
}

/*
 * Prepare a donation request in @res for the current PE's owned @sro.
 * If @seal is true, publish the context and relinquish ownership; otherwise
 * leave it owned by the caller. @state specifies the required donor state.
 */
static void tracking_sro_request_donation(struct sro_context *sro,
					  struct smc_result *res,
					  unsigned long state,
					  bool seal)
{
	unsigned long pending;

	assert((sro != NULL) && (res != NULL));
	pending = sro->tracking_ctx.requested_pages -
		  sro->tracking_ctx.transferred_pages;
	/* A peer may advance or reuse the context as soon as it is sealed. */
	/* NOLINTNEXTLINE(google-readability-casting) */
	sro->tracking_ctx.callback = (int)TRACKING_SRO_DONATE;
	res->x[0] = RMI_INCOMPLETE |
		    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_DONATE) |
		    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL);
	res->x[1] = seal ? sro_ctx_seal() : 0UL;
	res->x[2] = rmi_op_donate_req_encode(pending * GRANULE_SIZE,
					     RMI_OP_MEM_NON_CONTIG, state);
}

/*
 * Roll back all accepted metadata donors before reporting @status, which is
 * RMI_BLOCKED for an EL3 conflict or RMI_ERROR_INPUT for an invalid donation.
 * An accepted donor whose EL3 continuation failed remains NS and unmapped;
 * failed_donor_pa records it for return alongside the mapped donors.
 * The caller owns @sro. Return the next memory request through @res.
 */
static void tracking_sro_donation_abort(struct sro_context *sro,
					struct smc_result *res,
					unsigned long status)
{
	struct sro_tracking_ctx *ctx = &sro->tracking_ctx;

	ctx->ret_status = status;
	ctx->requested_pages = ctx->transferred_pages;
	ctx->reclaim_page = 0UL;
	/* NOLINTBEGIN(google-readability-casting) */
	ctx->callback = (ctx->transferred_pages == 0UL) ?
			(int)TRACKING_SRO_FINISH : (int)TRACKING_SRO_RECLAIM;
	/* NOLINTEND(google-readability-casting) */
	res->x[0] = RMI_INCOMPLETE |
		    INPLACE(RMI_OP_MEM_REQ, (ctx->transferred_pages == 0UL) ?
			    RMI_OP_MEM_REQ_NONE : RMI_OP_MEM_REQ_RECLAIM) |
		    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL);
	res->x[1] = ctx->transferred_pages;
	res->x[2] = 0UL;
}

/*
 * Select the next donation phase for the owned SRO. @consumed is the number
 * of pages accepted by this donation call, or zero for a continuation. A
 * pending EL3 operation must complete before requesting more backing pages.
 */
static void tracking_sro_donation_next(struct sro_context *sro,
				       struct smc_result *res, unsigned long consumed)
{
	struct sro_tracking_ctx *ctx = &sro->tracking_ctx;

	if (!ctx->gpi.pending && (ctx->transferred_pages < ctx->requested_pages)) {
		tracking_sro_request_donation(sro, res, sro->mem_state, false);
	} else {
		/* NOLINTBEGIN(google-readability-casting) */
		ctx->callback = ctx->gpi.pending ? (int)TRACKING_SRO_DELEGATE_CONTINUE :
						  (int)TRACKING_SRO_CONTINUE;
		/* NOLINTEND(google-readability-casting) */
		res->x[0] = RMI_INCOMPLETE |
			    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_NONE) |
			    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL);
		res->x[2] = 0UL;
	}
	res->x[1] = consumed;
}

/*
 * Complete delegation of the last accepted, still-unmapped donor. The SRO
 * retains its PA and EL3 state across RMI_OP_CONTINUE. Map only a fully
 * delegated page. An EL3 conflict reclaims all accepted donors before returning
 * RMI_BLOCKED; other failures reclaim them before returning RMI_ERROR_INPUT.
 * A donor still in NS PAS is returned untouched. Return the next SRO request
 * in @res, retaining the transition marker until final completion.
 */
static void tracking_sro_delegate_continue(unsigned long fid __unused,
					   struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	struct sro_tracking_ctx *ctx;
	int ret;

	assert((sro != NULL) && (fid == SMC_RMI_OP_CONTINUE));
	ctx = &sro->tracking_ctx;
	assert(ctx->gpi.pending && (ctx->transferred_pages != 0UL));
	ret = tracking_sro_gpi_step(ctx, ctx->gpi.pa, true);
	if (ctx->gpi.el3.incomplete) {
		tracking_sro_donation_next(sro, res, 0UL);
		return;
	}
	if (ctx->gpi.processed_size == GRANULE_SIZE) {
		uintptr_t va = tracking_sro_page_va(ctx, ctx->transferred_pages - 1UL);
		int map_ret __unused = tracking_region_page_populate(va, ctx->gpi.pa);

		assert(map_ret == 0);
		ctx->gpi.pending = false;
		if (ret == E_RMM_AGAIN) {
			/* Include any completed delegation in the conflict rollback. */
			tracking_sro_donation_abort(sro, res, RMI_BLOCKED);
			return;
		}
	} else if (ret != E_RMM_BUSY) {
		/* This accepted page never reached Realm PAS and must not be accessed. */
		ctx->failed_donor_pa = ctx->gpi.pa;
		ctx->failed_donor = true;
		ctx->gpi.pending = false;
		tracking_sro_donation_abort(sro, res,
				(ret == E_RMM_AGAIN) ? RMI_BLOCKED : RMI_ERROR_INPUT);
		return;
	}
	tracking_sro_donation_next(sro, res, 0UL);
}

/*
 * Consume donated address-list blocks and install their constituent granules.
 *
 * An input descriptor may represent a block larger than one granule. Claiming
 * and mapping tracking metadata are granule-sized operations, so expand each
 * block and install its granules in address-list order. Report the number of
 * granules consumed from this donation call through @res.
 * BUSY leaves the current page unconsumed and requests another donation call.
 * A conflict leaves it unconsumed and reclaims earlier accepted pages before
 * reporting RMI_BLOCKED; invalid donors similarly terminate with RMI_ERROR_INPUT.
 * The Host retains the unconsumed page and any following input pages.
 * INCOMPLETE consumes the pending page and requests RMI_OP_CONTINUE; the Host
 * retains only the following pages, which have not yet been submitted to EL3.
 */
static void tracking_sro_donate(unsigned long fid __unused,
				struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	struct sro_tracking_ctx *ctx;
	unsigned long consumed = 0UL;
	unsigned long pa;
	unsigned long state;
	unsigned long ret = RMI_SUCCESS;
	int level;

	assert((sro != NULL) && (fid == SMC_RMI_OP_MEM_DONATE));
	ctx = &sro->tracking_ctx;
	while ((ctx->transferred_pages < ctx->requested_pages) &&
	       addr_list_reduce_first_block(&sro->addr_list, &pa, &level,
					    &state)) {
		unsigned long block_pages = XLAT_BLOCK_SIZE(level) / GRANULE_SIZE;

		/* The SRO framework bounds the complete donation by this request. */
		assert(block_pages <=
		       (ctx->requested_pages - ctx->transferred_pages));
		/* Claim and map every granule represented by this block. */
		for (unsigned long i = 0UL; i < block_pages; i++) {
			ret = tracking_sro_page_add(ctx,
					pa + (i * GRANULE_SIZE), state);
			if (ret != RMI_SUCCESS) {
				break;
			}
			consumed++;
			if (ctx->gpi.pending) {
				break;
			}
		}
		if ((ret != RMI_SUCCESS) || ctx->gpi.pending) {
			break;
		}
	}

	if ((ret != RMI_SUCCESS) && (ret != RMI_BUSY)) {
		tracking_sro_donation_abort(sro, res, ret);
		return;
	}
	tracking_sro_donation_next(sro, res, consumed);
}

/*
 * Clear every donated page before initializing the tracking arrays.
 * All requested pages must already be delegated and mapped at granule-aligned
 * VAs, as required by granule_memzero_mapped().
 */
static void tracking_sro_pages_clear(const struct sro_tracking_ctx *ctx)
{
	assert((ctx != NULL) &&
	       (ctx->transferred_pages == ctx->requested_pages));
	for (unsigned long i = 0UL; i < ctx->requested_pages; i++) {
		granule_memzero_mapped((void *)tracking_sro_page_va(ctx, i));
	}
}

/*
 * Finalize a successful SET_TRACKING transition to fine tracking.
 *
 * @ctx describes a completed TRACKING_SRO_SET_DONATE operation and @tr is its
 * target region. Donated metadata outside @tr was marked INTERNAL when it was
 * claimed. A donated page inside @tr is self-describing, so its fine granule
 * became available only when the transition installed the fine representation.
 * Mark each such granule INTERNAL before exposing the representation.
 *
 * This function takes @tr's write lock and clears the transition marker only
 * after all self-describing granules have been initialized.
 */
static void tracking_sro_fine_transition_complete(
					const struct sro_tracking_ctx *ctx,
					struct tracking_region *tr)
{
	assert((ctx != NULL) && (tr != NULL));
	tracking_region_write_lock(tr);
	for (unsigned long i = 0UL; i < ctx->requested_pages; i++) {
		uintptr_t va = tracking_sro_page_va(ctx, i);
		uintptr_t pa = tracking_region_page_to_pa(va);

		if (tracking_sro_page_is_self_describing(ctx, pa)) {
			tracking_region_fine_descriptor_init_internal_locked(tr, pa);
		}
	}
	tracking_region_transition_set_locked(tr, false);
	tracking_region_write_unlock(tr);
}

/*
 * Complete a SET_TRACKING transition after fine-metadata donation.
 *
 * The SRO framework calls this function for RMI_OP_CONTINUE after every
 * requested metadata page has been donated and mapped. Clear the pages before
 * using them as tracking metadata. Install the target fine representation;
 * on failure, reclaim the donated pages before reporting the error to the
 * Host. Lock contention yields with no memory request and retains the donated
 * pages for another continuation.
 *
 * On a successful SET_TRACKING transition, initialize any self-describing
 * metadata granules and release the region's transition marker. Return the
 * operation status through @res.
 */
static void tracking_sro_continue(unsigned long fid __unused,
				  struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	struct sro_tracking_ctx *ctx;
	unsigned long ret;
	struct tracking_region *tr = NULL;
	bool found __unused;
	unsigned long tr_idx __unused;

	assert((sro != NULL) && (fid == SMC_RMI_OP_CONTINUE));
	ctx = &sro->tracking_ctx;
	tracking_sro_pages_clear(ctx);

	assert(ctx->operation == (int)TRACKING_SRO_SET_DONATE);
	ret = tracking_region_set_tracking_owned(ctx->addr, ctx->category,
						 ctx->target_state);
	if (ret == RMI_BUSY) {
		/* Preserve donated metadata and retry after existing users finish. */
		res->x[0] = RMI_INCOMPLETE |
			    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_NONE) |
			    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL);
		res->x[1] = 0UL;
		res->x[2] = 0UL;
		return;
	}
	if (ret != RMI_SUCCESS) {
		/* Donated mappings must be returned before exposing the error. */
		ctx->ret_status = ret;
		ctx->reclaim_page = 0UL;
		/* NOLINTNEXTLINE(google-readability-casting) */
		ctx->callback = (int)TRACKING_SRO_RECLAIM;
		res->x[0] = RMI_INCOMPLETE |
			    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_RECLAIM) |
			    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL);
		res->x[1] = 0UL;
		res->x[2] = 0UL;
		return;
	}

	/*
	 * The transition created granules for self-describing backing pages.
	 * Mark them INTERNAL before releasing the transition marker.
	 */
	found = tracking_region_set_tracking_find(ctx->addr, ctx->category,
						  &tr_idx, &tr);
	assert(found);
	tracking_sro_fine_transition_complete(ctx, tr);
	res->x[0] = RMI_SUCCESS;
}

/*
 * Select the reclaim state of self-describing backing while the owning SRO
 * retains the transition marker. A delegated coarse region keeps Realm PAS;
 * an untracked or NS coarse region requires return to Non-secure PAS.
 * Return the corresponding RMI_OP_MEM state. The owning SRO must retain a
 * valid source representation until its backing has been reclaimed.
 */
static unsigned long tracking_sro_self_describing_reclaim(const struct sro_tracking_ctx *ctx)
{
	unsigned long state = RMI_OP_MEM_DELEGATED;
	bool valid __unused;

	assert(ctx != NULL);
	valid = tracking_sro_self_describing_state(ctx, &state);
	assert(valid);
	return state;
}

/*
 * Return one tracking-metadata page to the Host.
 *
 * @sro describes a SET_TRACKING metadata reclaim or donation rollback.
 * @page is the logical index of an accepted page in that transfer.
 * Clear and unmap the page before changing its PAS or returning ownership.
 * Self-describing backing is restored to the state represented by the target
 * region; all other fine-metadata backing is restored to DELEGATED.
 *
 * Append its PA and restored RMI memory state to the reclaim address list.
 * Non-self-describing pages remain owned in INTERNAL state through unmapping,
 * so their granules are usable even while their own tracking region has
 * a pending transition.
 * Return false while EL3 is incomplete, retaining the unmapped page and cookie.
 * Stateless BUSY restores the mapping for a fresh request. Reclaim owns the
 * page, so an EL3 conflict or rejection violates the undelegation contract.
 * An accepted donor rejected during continuation is already NS and is returned
 * untouched.
 * Return true only after appending a successfully reclaimed page to the list.
 */
static bool tracking_sro_reclaim_page(struct sro_context *sro,
				      unsigned long page)
{
	struct sro_tracking_ctx *ctx = &sro->tracking_ctx;
	uintptr_t va = tracking_sro_page_va(ctx, page);
	uintptr_t pa;
	unsigned long state;
	bool added __unused;
	int ret __unused;

	if (ctx->failed_donor && (page == (ctx->transferred_pages - 1UL))) {
		/* Failed continuation left the last accepted donor NS and unmapped. */
		pa = ctx->failed_donor_pa;
		state = RMI_OP_MEM_UNDELEGATED;
		ctx->failed_donor = false;
		goto publish;
	}
	if (ctx->gpi.pending) {
		/* The page stays unmapped while EL3 retains its operation. */
		pa = ctx->gpi.pa;
	} else {
		pa = tracking_region_page_to_pa(va);
		(void)memset((void *)va, 0, GRANULE_SIZE);
		/* Remove the alias before PoE maintenance or releasing the backing page. */
		ret = tracking_region_page_depopulate(va);
		assert(ret == 0);
	}

	if (tracking_sro_page_is_self_describing(ctx, pa)) {
		state = tracking_sro_self_describing_reclaim(ctx);
	} else {
		struct granule *g;

		g = tr_addr_to_granule(pa);
		granule_lock(g, GRANULE_STATE_INTERNAL);
		granule_unlock_transition_to_delegated(g);
		state = RMI_OP_MEM_DELEGATED;
	}

	if (state == RMI_OP_MEM_UNDELEGATED) {
		ret = tracking_sro_gpi_step(ctx, pa, false);
		if (ctx->gpi.el3.incomplete) {
			return false;
		}
		ctx->gpi.pending = false;
		if (ctx->gpi.processed_size == 0UL) {
			/* Stateless BUSY left the owned page in Realm PAS; restore its mapping. */
			assert(ret == E_RMM_BUSY);
			ret = tracking_region_page_populate(va, pa);
			assert(ret == 0);
			return false;
		}
		assert(ctx->gpi.processed_size == GRANULE_SIZE);
	}

publish:
	added = addr_list_add_block(&sro->addr_list, pa,
				    XLAT_TABLE_LEVEL_MAX, state);
	assert(added);
	return true;
}

/*
 * Return the next batch of tracking-metadata pages to the Host.
 *
 * The SRO framework calls this function for RMI_OP_MEM_RECLAIM when rolling
 * back a failed fine-metadata donation, and after a successful
 * transition away from fine tracking. Starting at @ctx->reclaim_page, remove
 * each page's metadata mapping, restore its Host-visible memory state and
 * append its PA and state to the output address list. Limit the batch to the
 * number of descriptors available in that list.
 * Stop on an incomplete EL3 operation or contention without advancing the
 * pending page or reporting it as reclaimed. The next RMI_OP_MEM_RECLAIM
 * resumes it through the shared EL3 helper, retaining any continuation cookie.
 *
 * Keep the SRO non-cancellable while pages remain. Once every page has been
 * returned, request no further memory operation and select TRACKING_SRO_FINISH
 * so that the following RMI_OP_CONTINUE can finish the SRO, release the
 * SET_TRACKING transition marker when applicable, and report the final status
 * through @res.
 */
static void tracking_sro_reclaim(unsigned long fid __unused,
				 struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	struct sro_tracking_ctx *ctx;
	unsigned long count;
	unsigned long reclaimed = 0UL;

	assert((sro != NULL) && (fid == SMC_RMI_OP_MEM_RECLAIM));
	ctx = &sro->tracking_ctx;
	count = MIN(ctx->requested_pages - ctx->reclaim_page,
		    sro_ctx_range_desc_count(sro));
	for (unsigned long i = 0UL; i < count; i++) {
		if (!tracking_sro_reclaim_page(sro, ctx->reclaim_page)) {
			break;
		}
		ctx->reclaim_page++;
		reclaimed++;
	}

	res->x[0] = RMI_INCOMPLETE |
		    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL);
	res->x[1] = reclaimed;
	res->x[2] = 0UL;
	if (ctx->reclaim_page == ctx->requested_pages) {
		res->x[0] |= INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_NONE);
		/* NOLINTNEXTLINE(google-readability-casting) */
		ctx->callback = (int)TRACKING_SRO_FINISH;
	} else {
		res->x[0] |= INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_RECLAIM);
	}
}

/* Finish a reclaim SRO and make the tracking region available again. */
static void tracking_sro_finish(unsigned long fid __unused,
				struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	struct tracking_region *tr = NULL;
	bool found __unused;
	unsigned long tr_idx __unused;

	assert((sro != NULL) && (fid == SMC_RMI_OP_CONTINUE));
	assert(sro->init_command == SMC_RMI_GRANULE_TRACKING_SET);
	found = tracking_region_set_tracking_find(sro->tracking_ctx.addr,
						  sro->tracking_ctx.category,
						  &tr_idx, &tr);
	assert(found);
	tracking_region_write_lock(tr);
	tracking_region_transition_set_locked(tr, false);
	tracking_region_write_unlock(tr);
	res->x[0] = sro->tracking_ctx.ret_status;
}

/* Clear a transition marker after a failed SRO setup. */
static void tracking_sro_region_release(struct tracking_region *tr)
{
	assert(tr != NULL);
	tracking_region_write_lock(tr);
	tracking_region_transition_set_locked(tr, false);
	tracking_region_write_unlock(tr);
}

/*
 * Initialize a reserved SET_TRACKING SRO context. @operation must select
 * TRACKING_SRO_SET_DONATE or TRACKING_SRO_SET_RECLAIM; @pages and @array_mask
 * describe the metadata transfer required by the claimed transition.
 */
static void tracking_sro_set_context_init(struct sro_context *sro,
					  unsigned long addr,
					  unsigned long tr_idx,
					  unsigned long category,
					  unsigned long state,
					  unsigned long pages,
					  unsigned int array_mask,
					  enum tracking_sro_operation operation)
{
	assert(sro != NULL);
	sro->tracking_ctx.addr = addr;
	sro->tracking_ctx.tr_idx = tr_idx;
	sro->tracking_ctx.category = category;
	sro->tracking_ctx.target_state = state;
	sro->tracking_ctx.ret_status = RMI_SUCCESS;
	sro->tracking_ctx.requested_pages = pages;
	sro->tracking_ctx.transferred_pages = 0UL;
	sro->tracking_ctx.reclaim_page = 0UL;
	sro->tracking_ctx.array_mask = array_mask;
	sro->tracking_ctx.operation = (int)operation;
}

/*
 * Process a SET_TRACKING request, using an SRO when fine-granule backing
 * must be transferred.
 *
 * When entering fine tracking, request all required backing pages before
 * installing the fine representation. When leaving fine tracking, install the
 * target representation before returning the inactive fine backing to the
 * Host. Either direction transfers at least one page. Unchanged tracking and
 * transitions between NONE and COARSE complete synchronously.
 *
 * Claim the region before inspecting its fine backing, so another transition
 * cannot reclaim or replace that backing before this operation uses it. The
 * marker remains set for the complete multi-call operation so competing
 * SET_TRACKING requests return RMI_BLOCKED until the Host completes that SRO.
 *
 * @addr, @category and @state identify the requested tracking transition.
 * Return the synchronous RMI status through @res, or RMI_INCOMPLETE with the
 * sealed SRO handle and the first donation or reclaim request.
 */
void tracking_region_set_sro(unsigned long addr,
			     unsigned long category,
			     unsigned long state,
			     struct smc_result *res)
{
	struct tracking_region *tr;
	struct sro_context *sro;
	enum tr_state current;
	unsigned long tr_idx;
	unsigned long pages;
	unsigned long ret;
	unsigned int array_mask;

	assert(res != NULL);
	res->x[0] = RMI_ERROR_INPUT;
	if ((state != RMI_TRACKING_NONE) &&
	    (state != RMI_TRACKING_FINE) &&
	    (state != RMI_TRACKING_COARSE)) {
		return;
	}
	/*
	 * Validate the address and category, and locate the struct tracking_region.
	 * Retain its shared index to locate the fine granule and
	 * dev_granule ranges for donation or reclaim.
	 */
	if (!tracking_region_set_tracking_find(addr, category, &tr_idx, &tr)) {
		return;
	}

	/*
	 * Take a preliminary state snapshot to select the transfer path. The
	 * region is not claimed yet, so the transition claim revalidates this state.
	 */
	tracking_region_read_lock(tr);
	current = tracking_region_get_state(tr);
	if (tracking_region_transition_pending(tr)) {
		tracking_region_read_unlock(tr);
		res->x[0] = RMI_BLOCKED;
		return;
	}
	tracking_region_read_unlock(tr);
	if ((unsigned long)current == state) {
		res->x[0] = RMI_SUCCESS;
		return;
	}

	if ((state != RMI_TRACKING_FINE) && (current != trs_fine)) {
		/* NONE-to-COARSE and COARSE-to-NONE do not transfer fine backing. */
		res->x[0] = tracking_region_set_tracking(addr, category, state);
		return;
	}

	/*
	 * Stabilize the fine-backing inventory before inspecting it. Claim also
	 * revalidates the state snapshot and every active source granule.
	 */
	ret = tracking_region_transition_claim(tr, addr, current,
					       (enum tr_state)state);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	if (state == RMI_TRACKING_FINE) {
		/* Fine backing must be present before its granules are initialized. */
		pages = tracking_region_fine_donation_setup(tr, tr_idx, &array_mask);
		ret = sro_ctx_reserve(SMC_RMI_GRANULE_TRACKING_SET,
				      pages * GRANULE_SIZE, false, false,
				      SMC_RMI_OP_MEM_DONATE);
	} else {
		/* Record the mapped fine backing to return after it becomes inactive. */
		pages = tracking_region_fine_reclaim_setup(tr, tr_idx, &array_mask);
		ret = sro_ctx_reserve(SMC_RMI_GRANULE_TRACKING_SET, 0UL,
				      false, false, SMC_RMI_OP_MEM_RECLAIM);
	}

	if (ret != RMI_SUCCESS) {
		tracking_sro_region_release(tr);
		res->x[0] = ret;
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);
	if (state == RMI_TRACKING_FINE) {
		/*
		 * Keep the region in its current NONE or COARSE tracking state until
		 * all fine-granule backing has been donated. CONDITIONAL allows a
		 * self-describing page to be UNDELEGATED for NONE, or to match the
		 * coarse granule for COARSE. All other donated pages must be DELEGATED.
		 */
		tracking_sro_set_context_init(sro, addr, tr_idx, category, state,
					      pages, array_mask,
					      TRACKING_SRO_SET_DONATE);
		sro->mem_state = RMI_OP_MEM_CONDITIONAL;
		tracking_sro_request_donation(sro, res,
					      RMI_OP_MEM_CONDITIONAL, true);
		return;
	}

	/*
	 * Change the region from FINE to the requested NONE or COARSE state while
	 * every page backing the fine arrays remains mapped. This allows the transition to
	 * lock and validate the complete fine state before it is discarded. The
	 * SRO owns the transition marker, so it may proceed while other
	 * SET_TRACKING requests are rejected.
	 */
	ret = tracking_region_set_tracking_owned(addr, category, state);
	if (ret != RMI_SUCCESS) {
		tracking_sro_region_release(tr);
		sro_ctx_release();
		res->x[0] = ret;
		return;
	}

	tracking_sro_set_context_init(sro, addr, tr_idx, category, state, pages,
				      array_mask, TRACKING_SRO_SET_RECLAIM);
	/* NOLINTNEXTLINE(google-readability-casting) */
	sro->tracking_ctx.callback = (int)TRACKING_SRO_RECLAIM;
	/* Fine backing is now inactive and can be returned in reclaim batches. */
	res->x[0] = RMI_INCOMPLETE |
		    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_RECLAIM) |
		    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CANNOT_CANCEL);
	res->x[1] = sro_ctx_seal();
	res->x[2] = 0UL;
}

/*
 * Dispatch the next callback for a SET_TRACKING metadata transfer.
 * The generic SRO layer must have assigned the sealed context to this PE.
 * @res receives the next memory request or the terminal RMI result.
 */
void tracking_region_sro_handler(unsigned long fid, struct smc_result *res)
{
	static const sro_handle_cb callbacks[] = {
		[TRACKING_SRO_DONATE] = tracking_sro_donate,
		[TRACKING_SRO_DELEGATE_CONTINUE] = tracking_sro_delegate_continue,
		[TRACKING_SRO_CONTINUE] = tracking_sro_continue,
		[TRACKING_SRO_RECLAIM] = tracking_sro_reclaim,
		[TRACKING_SRO_FINISH] = tracking_sro_finish
	};
	struct sro_context *sro = my_sro_ctx();

	assert((sro != NULL) && (res != NULL));
	assert((sro->tracking_ctx.callback >= 0) &&
	       (sro->tracking_ctx.callback < (int)ARRAY_SIZE(callbacks)));
	callbacks[sro->tracking_ctx.callback](fid, res);
}

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

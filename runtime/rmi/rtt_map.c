/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <addr_list.h>
#include <arch_helpers.h>
#include <assert.h>
#include <buffer.h>
#include <dev.h>
#include <dev_granule.h>
#include <granule.h>
#include <measurement.h>
#include <realm.h>
#include <rtt_internal.h>
#include <s2tt.h>
#include <s2tt_ap.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <sro_context.h>
#include <status.h>
#include <stdbool.h>
#include <stddef.h>

/*
 * Map/Unmap commands can operate up to a level 1 block entry so min_level is
 * the smallest block size.
 */
static bool validate_rtt_map_cmds(unsigned long map_addr,
				  long level,
				  struct rd *rd)
{
	if ((level < S2TT_MIN_BLOCK_LEVEL) || (level > S2TT_PAGE_LEVEL)) {
		return false;
	}
	return validate_map_addr(map_addr, level, rd);
}

/*
 * Finalize the partial-progress result of a range-aware map command.
 * If at least one block was mapped (@out_top > @base), return
 * RMI_SUCCESS: the host treats the call as partial progress regardless
 * of which per-block error stopped the loop. Populate res->x[1] only
 * when the final return value is RMI_SUCCESS; otherwise leave it
 * untouched (per IPBSPY: out_top is UNKNOWN on error).
 *
 * Shared by range-aware map entry / continue paths.
 */
static unsigned long map_partial_progress_finalize(struct smc_result *res,
						   unsigned long ret,
						   unsigned long out_top,
						   unsigned long base)
{
	if (out_top > base) {
		ret = RMI_SUCCESS;
	}

	if (ret == RMI_SUCCESS) {
		res->x[1] = out_top;
	}

	return ret;
}

/*
 * Shared input validator for the range-aware map commands
 * (RMI_RTT_DATA_MAP, RMI_RTT_UNPROT_MAP, RMI_RTT_DEV_MAP). Rejects
 * realms not in NEW or ACTIVE state, then builds the descriptor list,
 * derives the walk level/block size from the first descriptor, and
 * runs the common range checks against @rd.
 *
 * Parameters that select per-command behaviour:
 *   @oaddr_type     - already extracted from the per-command flags
 *                     word (RMI_ADDR_TYPE_SINGLE / RMI_ADDR_TYPE_LIST).
 *   @list_count     - host-supplied flags.list_count value; the number
 *                     of descriptor slots to read from the host
 *                     granule at @oaddr. Ignored unless
 *                     @oaddr_type == RMI_ADDR_TYPE_LIST. Must be in
 *                     (0, ADDR_LIST_MAX_RANGES]; further clipped to
 *                     the slots remaining between @oaddr and the end
 *                     of its NS granule.
 *   @oaddr          - SINGLE: the single descriptor; LIST: NS PA of
 *                     a granule containing descriptors.
 *   @expected_state - state every descriptor must report:
 *                     RMI_OP_MEM_DELEGATED for DATA_MAP,
 *                     RMI_OP_MEM_UNDELEGATED for UNPROT_MAP.
 *   @must_be_in_par - true: range must lie inside PAR (DATA_MAP);
 *                     false: range must lie outside PAR (UNPROT_MAP).
 *
 * Returns RMI_SUCCESS with @list_out / @level_out / @map_size_out
 * populated; on failure returns the RMI status to surface in res->x[0].
 * Per-descriptor / per-entry checks (PA alignment to block size, level
 * mismatch on a later descriptor, leaf-RTT exhaustion) remain in the
 * walk loop because they depend on walk state.
 */
static unsigned long validate_map_inputs_common(unsigned long base,
						unsigned long top,
						unsigned long oaddr_type,
						unsigned long list_count,
						unsigned long oaddr,
						struct rd *rd,
						unsigned long expected_state,
						bool must_be_in_par,
						struct addr_list *list_out,
						long *level_out,
						unsigned long *map_size_out)
{
	unsigned long first_addr, cnt, st;
	unsigned long map_size;
	long level;
	int first_level;
	bool in_par;

	if ((get_rd_state_locked(rd) != REALM_NEW) &&
	    (get_rd_state_locked(rd) != REALM_ACTIVE)) {
		return RMI_ERROR_REALM;
	}

	if (top <= base) {
		return RMI_ERROR_INPUT;
	}

	if (oaddr_type == RMI_ADDR_TYPE_SINGLE) {
		addr_list_init(list_out, LIST_TYPE_INPUT, 1U);
		if (!addr_list_add_desc(list_out, oaddr)) {
			return RMI_ERROR_INPUT;
		}
	} else if (oaddr_type == RMI_ADDR_TYPE_LIST) {
		/*
		 * LIST: @oaddr is the NS PA of a granule containing
		 * descriptors; @list_count is the host-supplied number
		 * of valid entries. Reject 0 / out-of-range up front,
		 * then clip to the descriptor slots that fit between
		 * @oaddr and the end of its granule.
		 */
		unsigned long offset = oaddr & (GRANULE_SIZE - 1UL);
		unsigned long granule_remaining;

		if (!ALIGNED(offset, sizeof(unsigned long))) {
			return RMI_ERROR_INPUT;
		}
		granule_remaining = (GRANULE_SIZE - offset) /
					sizeof(unsigned long);
		list_count = MIN(list_count, granule_remaining);
		if (list_count == 0UL) {
			return RMI_ERROR_INPUT;
		}
		addr_list_init(list_out, LIST_TYPE_INPUT,
			       (unsigned int)list_count);
		if (!addr_list_copy_from_host(list_out, oaddr,
					      (unsigned int)list_count)) {
			return RMI_ERROR_INPUT;
		}
	} else {
		return RMI_ERROR_INPUT;
	}

	/*
	 * Derive walk level from the first descriptor's SZ field. All
	 * descriptors processed in this call must use the same level; a
	 * mismatch on a later descriptor stops the iteration but is not
	 * a validator failure (the host gets partial progress).
	 */
	if (!addr_list_peek_desc(list_out, 0U, &first_addr, &first_level,
				 &cnt, &st)) {
		return RMI_ERROR_INPUT;
	}

	level = (long)first_level;

	if (st != expected_state) {
		return RMI_ERROR_INPUT;
	}

	map_size = s2tte_map_size(level);

	in_par = addr_in_par(rd, base) &&
		 addr_in_par(rd, top - GRANULE_SIZE);

	if (!validate_rtt_map_cmds(base, level, rd) ||
	    !validate_map_addr(top - GRANULE_SIZE, S2TT_PAGE_LEVEL, rd) ||
	    (in_par != must_be_in_par)) {
		return RMI_ERROR_INPUT;
	}

	if ((top - base) < map_size) {
		return pack_return_code(RMI_ERROR_RTT, (unsigned char)level);
	}

	*level_out = level;
	*map_size_out = map_size;
	return RMI_SUCCESS;
}
/*
 * Pop the next descriptor from @list and run the per-block prologue
 * shared by the range-aware map walk loops:
 *
 *   1. Yield on pending physical IRQ. *@yield_out is set to true and
 *      RMI_SUCCESS is returned; the caller treats this as "stop and
 *      report partial progress".
 *   2. Reduce one block descriptor in the list.
 *   3. Descriptor state must equal @expected_state.
 *   4. Descriptor level must equal the walk @level (single tree shape
 *      per call).
 *   5. Block must fit in the remaining range (@out_top + @map_size
 *      must not exceed @top).
 *   6. PA must be aligned to the block size.
 *
 * On full success: *@yield_out == false, *@pa_out is the block PA, and
 * the caller proceeds with the per-command mapping primitive.
 *
 * On any failure: returns the RMI status the loop should bail with
 * (RMI_ERROR_INPUT for malformed input, or pack_return_code(
 * RMI_ERROR_RTT, level) for "doesn't fit"); *@pa_out is UNSPECIFIED.
 */
static unsigned long map_pop_next_block(struct addr_list *list,
					struct s2tt_context *s2_ctx,
					unsigned long expected_state,
					long level,
					unsigned long map_size,
					unsigned long out_top,
					unsigned long top,
					unsigned long *pa_out,
					bool *yield_out)
{
	unsigned long pa;
	unsigned long st;
	int desc_level;

	*yield_out = false;

	if (read_isr_el1() != 0UL) {
		*yield_out = true;
		return RMI_SUCCESS;
	}

	if (!addr_list_reduce_first_block(list, &pa, &desc_level, &st)) {
		return RMI_ERROR_INPUT;
	}

	if (st != expected_state) {
		return RMI_ERROR_INPUT;
	}

	if ((long)desc_level != level) {
		return pack_return_code(RMI_ERROR_RTT, (unsigned char)level);
	}

	if ((out_top + map_size) > top) {
		return pack_return_code(RMI_ERROR_RTT, (unsigned char)level);
	}

	if (!ALIGNED(pa, map_size)) {
		return RMI_ERROR_INPUT;
	}

	/*
	 * If LPA2 is disabled for the realm, the block's PA range must
	 * fit in S2TT_MAX_PA_BITS. @pa is already aligned to @map_size,
	 * so checking the end address is sufficient.
	 */
	if (!s2_ctx->enable_lpa2 &&
	    ((pa + map_size) > (UL(1) << S2TT_MAX_PA_BITS))) {
		return RMI_ERROR_INPUT;
	}

	*pa_out = pa;
	return RMI_SUCCESS;
}
/*
 * Roll back a drain-time failure after the leaf slot has been stamped.
 * Every granule below @ctx->pending_off was drained by this SRO. Walk
 * the cursor backwards, returning each granule to DELEGATED. On a
 * pending IRQ leave @ctx->pending_off pointing to the remaining rollback
 * span and return with *@yielded set so RMI_OP_CONTINUE can resume.
 * Once the cursor reaches zero, clear the leaf marker, drop the
 * refcount taken when the marker was stamped, and return @ctx->ret_err.
 *
 * Caller contract: @ctx->g_llt is locked and @s2tt is its mapping.
 */
static unsigned long data_map_rollback_pending(struct sro_map_ctx *ctx,
					       unsigned long *s2tt,
					       bool *yielded)
{
	unsigned long stamped;

	*yielded = false;

	while (ctx->pending_off > 0UL) {
		struct granule *g_data;

		if (read_isr_el1() != 0UL) {
			*yielded = true;
			return RMI_SUCCESS;
		}

		ctx->pending_off -= GRANULE_SIZE;

		g_data = find_lock_granule(ctx->pa + ctx->pending_off,
					   GRANULE_STATE_DATA);
		if (g_data != NULL) {
			granule_unlock_transition_to_delegated(g_data);
		}
	}

	stamped = s2tte_read(&s2tt[ctx->index]);
	assert(s2tte_drain_pending(stamped));
	assert(s2tte_drain_handle(stamped) == sro_ctx_my_handle());

	s2tte_write(&s2tt[ctx->index], s2tte_clear_drain_pending(stamped));
	atomic_granule_put_release(ctx->g_llt);

	ctx->rollback = false;
	return ctx->ret_err;
}

/*
 * Yieldable per-granule drain for an in-flight RMI_RTT_DATA_MAP block,
 * plus the finalize of the leaf s2tte on drain completion. Resumes from
 * @ctx->pending_off and advances it past every granule it has claimed
 * and zeroed. Each iteration:
 *
 *   1. Sample read_isr_el1(); on a pending physical IRQ return true
 *      with the cursor pointing at the next pending granule.
 *   2. find_lock_granule(pa, DELEGATED) and keep it locked.
 *      On failure switch to rollback. Rollback is also yieldable; when
 *      complete it clears the leaf marker and returns RMI_ERROR_INPUT.
 *   3. buffer_granule_mecid_map_zeroed(SLOT_REALM, s2_ctx->mecid):
 *      the slow part. Zeroes the locked granule under the realm's MEC,
 *      then transitions it to DATA and unlocks it.
 *
 * On drain completion the leaf s2tte at &s2tt[@ctx->index] is
 * rewritten from the drain-pending marker to the assigned form for
 * @ctx->pa, preserving RIPAS / AP from the still-stamped s2tte.
 *
 * Caller contract: the leaf RTT granule (@ctx->g_llt) is locked and
 * @s2tt is its mapping for the duration of the call. Called from
 * both data_map_one_entry (entry path) and data_map_continue_handler
 * (continue path); both arrange the lock+map before invoking.
 *
 * Returns RMI_SUCCESS with *@yielded set on IRQ-yield during drain or
 * rollback, RMI_SUCCESS with *@yielded clear when the cursor reaches
 * the block size for @ctx->level (drain complete, s2tte finalized), or
 * RMI_ERROR_INPUT if a backing granule cannot be claimed and rollback
 * has completed.
 */
static unsigned long data_map_drain_pending(struct sro_map_ctx *ctx,
					    const struct s2tt_context *s2_ctx,
					    unsigned long *s2tt,
					    bool *yielded)
{
	unsigned long map_size = s2tte_map_size(ctx->level);
	unsigned long stamped, new_s2tte;

	*yielded = false;

	if (ctx->rollback) {
		return data_map_rollback_pending(ctx, s2tt, yielded);
	}

	while (ctx->pending_off < map_size) {
		struct granule *g_data;
		void *data;

		if (read_isr_el1() != 0UL) {
			*yielded = true;
			return RMI_SUCCESS;
		}

		g_data = find_lock_granule(ctx->pa + ctx->pending_off,
					   GRANULE_STATE_DELEGATED);
		if (g_data == NULL) {
			ctx->rollback = true;
			ctx->ret_err = RMI_ERROR_INPUT;
			return data_map_rollback_pending(ctx, s2tt, yielded);
		}

		data = buffer_granule_mecid_map_zeroed(g_data, SLOT_REALM,
						       s2_ctx->mecid);
		buffer_unmap(data);
		granule_unlock_transition(g_data, GRANULE_STATE_DATA);

		ctx->pending_off += GRANULE_SIZE;
	}

	stamped = s2tte_read(&s2tt[ctx->index]);
	assert(s2tte_drain_pending(stamped));
	assert(s2tte_drain_handle(stamped) == sro_ctx_my_handle());

	new_s2tte = s2tte_create_assigned_unchanged(s2_ctx,
				s2tte_clear_drain_pending(stamped),
				ctx->pa, ctx->level);
	s2tte_write(&s2tt[ctx->index], new_s2tte);

	return RMI_SUCCESS;
}

/*
 * Map one block of DELEGATED memory at @pa as DATA into the leaf RTT
 * slot &s2tt[index] (already locked and mapped) at level @level. The
 * block covers s2tte_map_size(@level) bytes and is backed by
 * map_size / GRANULE_SIZE consecutive granules starting at @pa.
 *
 * This function performs only the prepare phases (validate + stamp the
 * leaf s2tte with the drain-pending marker carrying the current SRO
 * handle + take one refcount on @g_llt).
 *
 * Sequence:
 *
 *   1. Stamp the leaf s2tte with S2TTE_SW_DRAIN_PENDING + the SRO
 *      handle. The architectural form stays unassigned so concurrent
 *      RIPAS / map / unmap callers see RMI_BUSY / -EAGAIN via the
 *      existing s2tte_drain_pending() checks. Take one refcount on
 *      @g_llt: it pins the leaf across yields and is the same
 *      refcount the finalized live mapping retains.
 *   2. The drain phase zeroes then transitions each backing granule
 *      from DELEGATED to DATA. On the first transition failure the
 *      drain rolls back the granules already taken, clears the marker
 *      and returns RMI_ERROR_INPUT.
 *
 * Returns:
 *   RMI_SUCCESS      slot prepared. *@need_drain is true if the slot
 *                    was stamped and the caller must populate the SRO
 *                    ctx and invoke data_map_drain_pending(); false
 *                    if the slot was already mapped to the requested
 *                    PA (idempotent, nothing to do).
 *   RMI_BUSY         slot still owes deferred maintenance from a
 *                    previous SRO (concurrent unmap drain in flight).
 *   pack_return_code(RMI_ERROR_RTT, level) slot is not unassigned, or
 *                    is already assigned to a different PA.
 *
 * On any non-success return *@need_drain is left undefined.
 */
static unsigned long data_map_one_entry(struct s2tt_context *s2_ctx,
					unsigned long *s2tt,
					unsigned long index,
					struct granule *g_llt,
					unsigned long pa,
					long level,
					bool *need_drain)
{
	unsigned long s2tte, stamped;

	s2tte = s2tte_read(&s2tt[index]);
	if (s2tte_is_assigned_ram(s2_ctx, s2tte, level) ||
	    s2tte_is_assigned_empty(s2_ctx, s2tte, level) ||
	    s2tte_is_assigned_destroyed(s2_ctx, s2tte, level)) {
		/*
		 * Already mapped: only treat as idempotent success if
		 * the existing OA matches the requested PA, otherwise
		 * report an RTT error.
		 */
		if (s2tte_pa(s2_ctx, s2tte, level) != pa) {
			return pack_return_code(RMI_ERROR_RTT,
						(unsigned char)level);
		}
		*need_drain = false;
		return RMI_SUCCESS;
	}
	if (!s2tte_is_unassigned(s2_ctx, s2tte)) {
		return pack_return_code(RMI_ERROR_RTT,
					(unsigned char)level);
	}
	if (s2tte_drain_pending(s2tte)) {
		return RMI_BUSY;
	}

	/*
	 * Stamp the leaf s2tte with the SRO handle + drain
	 * pending bit.
	 */
	stamped = s2tte_set_drain_pending(s2tte, sro_ctx_my_handle());
	s2tte_write(&s2tt[index], stamped);
	atomic_granule_get(g_llt);

	*need_drain = true;
	return RMI_SUCCESS;
}

/*
 * Validate inputs to RMI_RTT_DATA_MAP. Thin wrapper around
 * validate_map_inputs_common() that decodes RmiRttProtMapFlags
 * (OADDR_TYPE / LIST_COUNT). Descriptors must carry
 * RMI_OP_MEM_DELEGATED and the range must lie inside PAR.
 */
static unsigned long validate_data_map_inputs(unsigned long base,
					      unsigned long top,
					      unsigned long flags,
					      unsigned long oaddr,
					      struct rd *rd,
					      struct addr_list *list_out,
					      long *level_out,
					      unsigned long *map_size_out)
{
	unsigned long oaddr_type = EXTRACT(
			RMI_RTT_PROT_MAP_FLAGS_OADDR_TYPE, flags);
	unsigned long list_count = EXTRACT(
			RMI_RTT_PROT_MAP_FLAGS_LIST_COUNT, flags);

	return validate_map_inputs_common(base, top, oaddr_type, list_count,
					  oaddr, rd,
					  RMI_OP_MEM_DELEGATED,
					  /* must_be_in_par= */ true,
					  list_out, level_out, map_size_out);
}

/*
 * Initialize an SRO map context for a single in-flight block.
 * Called when a map helper has stamped the leaf s2tte with the
 * drain-pending marker and the per-granule drain is about to start.
 */
static void sro_map_ctx_init(struct sro_map_ctx *ctx,
			     struct granule *g_llt,
			     unsigned long rd_addr,
			     unsigned long pa,
			     unsigned long ipa,
			     unsigned long init_base,
			     unsigned long index,
			     long level)
{
	ctx->g_llt = g_llt;
	ctx->rd_addr = rd_addr;
	ctx->pa = pa;
	ctx->ipa = ipa;
	ctx->init_base = init_base;
	ctx->pending_off = 0UL;
	ctx->ret_err = RMI_SUCCESS;
	ctx->index = index;
	ctx->level = level;
	ctx->coh_type = DEV_MEM_MAX;
	ctx->rollback = false;
}

/*
 * Implements SMC_RMI_RTT_DATA_MAP with range support over a single leaf
 * RTT (one tree, one iteration). The level used for the walk is taken
 * from the SZ field of the first descriptor; if a subsequent descriptor
 * specifies a different level we stop and return the progress made so
 * far. Any other mismatch (alignment, level, granule state, RTT walk
 * stopping above the requested level, leaf-table exhaustion) also stops
 * the iteration and returns to the host.
 *
 * DATA_MAP stamps the leaf S2TTE with a drain-pending marker, then
 * runs a yieldable per-granule drain. Each backing granule is claimed
 * from DELEGATED, zeroed, and transitioned to DATA before the cursor
 * advances. On IRQ-yield the call seals an SRO context and returns
 * RMI_INCOMPLETE so the host can resume via RMI_OP_CONTINUE.
 *
 * @flags encodes RmiRttProtMapFlags (oaddr_type at bits 1:0,
 * list_count at bits 15:2). Other flag fields are ignored.
 *
 * Output on terminal progress:
 *   x[0] = RMI_SUCCESS | RMI_ERROR_*
 *   x[1] = out_top (IPA past the last successfully mapped block)
 *
 * Output on yield (drain of one block in flight):
 *   x[0] = RMI_INCOMPLETE | RMI_OP_MEM_REQ_NONE | RMI_OP_CANNOT_CANCEL
 *   x[1] = SRO context handle (pass to RMI_OP_CONTINUE).
 */
void smc_rtt_data_map(unsigned long rd_addr,
		      unsigned long base,
		      unsigned long top,
		      unsigned long flags,
		      unsigned long oaddr,
		      struct smc_result *res)
{
	struct addr_list list;
	struct granule *g_rd = NULL;
	struct rd *rd;
	struct s2tt_context s2_ctx;
	struct s2tt_walk wi;
	unsigned long *s2tt = NULL;
	unsigned long out_top = base;
	unsigned long ret;
	unsigned long map_size;
	unsigned long idx;
	long level;
	bool yielded = false;

	/* Reserve an SRO context up front. */
	ret = sro_ctx_reserve(SMC_RMI_RTT_DATA_MAP, 0UL, false, false,
			      SMC_RMI_OP_CONTINUE);
	if (ret != RMI_SUCCESS) {
		/* No SRO context to release: reserve itself failed. */
		res->x[0] = ret;
		return;
	}

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		ret = RMI_ERROR_INPUT;
		goto out_release_sro;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	ret = validate_data_map_inputs(base, top, flags, oaddr, rd,
				       &list, &level, &map_size);
	if (ret != RMI_SUCCESS) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		goto out_release_sro;
	}

	s2_ctx = rd->s2_ctx[PRIMARY_S2_CTX_ID];

	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);

	/*
	 * Root RTT now locked. The walk and per-block drain use only
	 * the stack copy of the primary S2 context.
	 */
	buffer_unmap(rd);
	granule_unlock(g_rd);

	s2tt_walk_lock_unlock(&s2_ctx, base, level, &wi);
	if (wi.last_level != level) {
		ret = pack_return_code(RMI_ERROR_RTT,
				       (unsigned char)wi.last_level);
		goto out_unlock_llt;
	}

	s2tt = buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx.mecid);
	assert(s2tt != NULL);

	/*
	 * Iterate blocks by popping one at a time from @list via
	 * map_pop_next_block(), which runs the common per-block prologue
	 * (IRQ yield / descriptor pop / state / level / bounds / PA
	 * alignment). Stop and return progress on any per-block error,
	 * on data_map_one_entry() failure, or on a mid-drain yield.
	 *
	 * On bail-out mid-iteration the popped block is discarded with
	 * the local @list; the host learns @out_top and reissues from
	 * there.
	 *
	 * @idx is the loop cursor; @wi.index is left at the walk's
	 * landing slot so it can be passed to helpers unchanged.
	 */
	for (idx = wi.index; idx < S2TTES_PER_S2TT; idx++) {
		unsigned long pa = 0UL;
		bool need_drain;
		bool yield;

		ret = map_pop_next_block(&list, &s2_ctx,
					 RMI_OP_MEM_DELEGATED,
					 level, map_size, out_top, top,
					 &pa, &yield);
		if (yield || (ret != RMI_SUCCESS)) {
			goto done;
		}

		ret = data_map_one_entry(&s2_ctx, s2tt, idx,
					 wi.g_llt, pa, level, &need_drain);
		if (ret != RMI_SUCCESS) {
			goto done;
		}

		if (need_drain) {
			/*
			 * Slot stamped. Populate the SRO ctx and run
			 * the yieldable per-granule drain. On
			 * IRQ-yield the leaf RTT is pinned by the refcount
			 * taken in data_map_one_entry() and the drain
			 * cursor lives in the SRO ctx.
			 */
			struct sro_map_ctx *ctx = &my_sro_ctx()->map_ctx;

			sro_map_ctx_init(ctx, wi.g_llt, rd_addr, pa,
					 out_top, base, idx, level);

			ret = data_map_drain_pending(ctx, &s2_ctx, s2tt,
						     &yielded);
			if (ret != RMI_SUCCESS) {
				goto done;
			}
			if (yielded) {
				goto done;
			}
			/* Drain finalized the slot; fall through. */
		}

		out_top += map_size;
	}

done:
	if (!yielded) {
		ret = map_partial_progress_finalize(res, ret, out_top, base);
	}
	/* Yielded path: @ret is overwritten below from sro_ctx_seal(). */

	buffer_unmap(s2tt);
out_unlock_llt:
	granule_unlock(wi.g_llt);
out_release_sro:
	if (yielded) {
		/*
		 * The refcount taken on wi.g_llt by data_map_one_entry()
		 * pins the leaf (and transitively the RTT chain and RD)
		 * until the SRO_CONTINUE drain finalizes the slot. No
		 * extra pin needed here.
		 */
		res->x[0] = RMI_INCOMPLETE |
			    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_NONE) |
			    INPLACE(RMI_OP_CAN_CANCEL_BIT,
				    RMI_OP_CANNOT_CANCEL);
		res->x[1] = (unsigned long)sro_ctx_seal();
		return;
	}

	sro_ctx_release();

	res->x[0] = ret;
}

/*
 * Implementation of RMI_RTT_DATA_MAP_INIT. Populates the delegated
 * granule @data_addr from the NS granule at @src_addr, measures it
 * under @flags, and installs an assigned_ram DATA mapping at
 * @map_addr in the realm identified by @rd_addr.
 */
unsigned long smc_rtt_data_map_init(unsigned long rd_addr,
				    unsigned long data_addr,
				    unsigned long map_addr,
				    unsigned long src_addr,
				    unsigned long flags)
{
	struct granule *g_data;
	struct granule *g_rd;
	struct granule *g_src;
	struct rd *rd;
	struct s2tt_walk wi;
	struct s2tt_context *s2_ctx;
	unsigned long s2tte, *s2tt;
	bool ns_access_ok;
	void *data;
	unsigned long ret;

	if ((flags != RMI_NO_MEASURE_CONTENT) &&
	    (flags != RMI_MEASURE_CONTENT)) {
		return RMI_ERROR_INPUT;
	}

	g_src = find_granule(src_addr);
	if ((g_src == NULL) ||
	    (granule_unlocked_state(g_src) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	if (!find_lock_two_granules(data_addr,
				    GRANULE_STATE_DELEGATED,
				    &g_data,
				    rd_addr,
				    GRANULE_STATE_RD,
				    &g_rd)) {
		return RMI_ERROR_INPUT;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (get_rd_state_locked(rd) != REALM_NEW) {
		ret = RMI_ERROR_REALM;
		goto out_unmap_rd;
	}

	if (!addr_in_par(rd, map_addr) ||
	    !validate_map_addr(map_addr, S2TT_PAGE_LEVEL, rd)) {
		ret = RMI_ERROR_INPUT;
		goto out_unmap_rd;
	}

	s2_ctx = &rd->s2_ctx[PRIMARY_S2_CTX_ID];

	/*
	 * If LPA2 is disabled for the realm, then `data_addr` must not be
	 * more than 48 bits wide.
	 */
	if (!s2_ctx->enable_lpa2 &&
	    (data_addr >= (UL(1) << S2TT_MAX_PA_BITS))) {
		ret = RMI_ERROR_INPUT;
		goto out_unmap_rd;
	}

	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	s2tt_walk_lock_unlock(s2_ctx, map_addr, S2TT_PAGE_LEVEL, &wi);
	if (wi.last_level != S2TT_PAGE_LEVEL) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned char)wi.last_level);
		goto out_unlock_ll_table;
	}

	s2tt = buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx->mecid);
	assert(s2tt != NULL);

	s2tte = s2tte_read(&s2tt[wi.index]);
	if (!s2tte_is_unassigned(s2_ctx, s2tte)) {
		ret = pack_return_code(RMI_ERROR_RTT,
					(unsigned char)S2TT_PAGE_LEVEL);
		goto out_unmap_ll_table;
	}

	/*
	 * Slot is architecturally unassigned but an in-flight
	 * RMI_RTT_DATA_MAP or RMI_RTT_DATA_UNMAP on another PE may
	 * still owe deferred maintenance against the OA that lived
	 * here. Both commands are permitted in REALM_NEW, so the
	 * marker is observable here. Bounce the host so it retries
	 * after the owning SRO finishes its drain.
	 */
	if (s2tte_drain_pending(s2tte)) {
		ret = RMI_BUSY;
		goto out_unmap_ll_table;
	}

	data = buffer_granule_mecid_map(g_data, SLOT_REALM, s2_ctx->mecid);
	assert(data != NULL);

	ns_access_ok = ns_buffer_read(SLOT_NS, g_src, 0U, GRANULE_SIZE, data);
	if (!ns_access_ok) {
		buffer_unmap(data);
		ret = RMI_ERROR_INPUT;
		goto out_unmap_ll_table;
	}

	measurement_data_granule_measure(
		rd->measurement[RIM_MEASUREMENT_SLOT],
		rd->algorithm,
		data,
		map_addr,
		flags);
	buffer_unmap(data);

	s2tte = s2tte_create_assigned_ram(s2_ctx, data_addr,
					  S2TT_PAGE_LEVEL, s2tte);
	s2tte_write(&s2tt[wi.index], s2tte);
	atomic_granule_get(wi.g_llt);

	ret = RMI_SUCCESS;

out_unmap_ll_table:
	buffer_unmap(s2tt);
out_unlock_ll_table:
	granule_unlock(wi.g_llt);
out_unmap_rd:
	buffer_unmap(rd);
	granule_unlock(g_rd);
	if (ret == RMI_SUCCESS) {
		granule_unlock_transition(g_data, GRANULE_STATE_DATA);
	} else {
		granule_unlock(g_data);
	}

	return ret;
}

/*
 * SRO continue callback for RMI_RTT_DATA_MAP. Invoked from
 * rmi_op_dispatch() in response to a host RMI_OP_CONTINUE on a sealed
 * handle. This callback resumes the deferred per-granule
 * transition and zero passes started by the entry call and, when
 * complete, finalizes the leaf s2tte to assigned_unchanged.
 *
 * The RD granule is locked before the leaf RTT to preserve the normal
 * RD -> RTT lock order. The extra refcount taken at stamp time (and
 * inherited as the live mapping's refcount on completion) pins the
 * leaf across the yield.
 *
 * Output on completion:
 *   x[0] = RMI_SUCCESS
 *   x[1] = IPA past the now-mapped block (host can continue mapping
 *          from this address with a fresh RMI_RTT_DATA_MAP call)
 *
 * Output on further yield:
 *   x[0] = RMI_INCOMPLETE | RMI_OP_MEM_REQ_NONE | RMI_OP_CANNOT_CANCEL
 *   x[1] = 0
 */
void data_map_continue_handler(unsigned long fid,
			       struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	struct sro_map_ctx *ctx;
	struct granule *g_rd;
	struct rd *rd;
	struct s2tt_context s2_ctx;
	unsigned long *s2tt;
	unsigned long ret;
	bool yielded;

	assert(sro != NULL);
	assert(fid == SMC_RMI_OP_CONTINUE);
	assert(sro->init_command == SMC_RMI_RTT_DATA_MAP);
	(void)fid;

	ctx = &sro->map_ctx;
	assert(ctx != NULL);
	assert(ctx->g_llt != NULL);

	/*
	 * Lock + map RD and the leaf RTT before resuming the drain so
	 * the drain sees the slot under the same contract as the entry
	 * path: the leaf granule is locked and @s2tt is its mapping for
	 * the duration of the call. The S2 context is copied before RD
	 * is released so the drain can run without keeping RD locked.
	 * On drain completion the drain itself finalizes the leaf s2tte;
	 * on yield the slot is left stamped with the drain-pending marker.
	 */
	g_rd = find_lock_granule(ctx->rd_addr, GRANULE_STATE_RD);
	assert(g_rd != NULL);
	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);
	s2_ctx = rd->s2_ctx[PRIMARY_S2_CTX_ID];

	granule_lock(ctx->g_llt, GRANULE_STATE_RTT);
	buffer_unmap(rd);
	granule_unlock(g_rd);

	s2tt = buffer_granule_mecid_map(ctx->g_llt, SLOT_RTT,
					s2_ctx.mecid);
	assert(s2tt != NULL);

	ret = data_map_drain_pending(ctx, &s2_ctx, s2tt, &yielded);

	buffer_unmap(s2tt);
	granule_unlock(ctx->g_llt);

	if (ret != RMI_SUCCESS) {
		/*
		 * Drain rolled back the in-flight block, but blocks
		 * committed by the entry call before its yield remain
		 * mapped. If any of those exist (ctx->ipa advanced past
		 * ctx->init_base) report partial progress as RMI_SUCCESS
		 * so the host learns the boundary from res->x[1].
		 */
		res->x[0] = map_partial_progress_finalize(res, ret,
							  ctx->ipa,
							  ctx->init_base);
		ctx->g_llt = NULL;
		return;
	}

	if (yielded) {
		/*
		 * Still pending; the leaf RTT is still pinned by the
		 * refcount taken at stamp time. Caller (smc_op_continue)
		 * re-seals the SRO context based on res->x[0] ==
		 * RMI_INCOMPLETE.
		 */
		res->x[0] = RMI_INCOMPLETE |
			    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_NONE) |
			    INPLACE(RMI_OP_CAN_CANCEL_BIT,
				    RMI_OP_CANNOT_CANCEL);
		res->x[1] = 0UL;
		return;
	}

	res->x[0] = RMI_SUCCESS;
	res->x[1] = ctx->ipa + s2tte_map_size(ctx->level);

	ctx->g_llt = NULL;
}

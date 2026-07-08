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

static bool rtt_map_irq_pending(void)
{
#ifdef RMM_RTT_MAP_CHECK_ISR_EL1
	return (read_isr_el1() != 0UL);
#else
	return false;
#endif
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
 *   1. If ISR_EL1 sampling is enabled, yield on pending physical IRQ.
 *      *@yield_out is set to true and RMI_SUCCESS is returned; the
 *      caller treats this as "stop and report partial progress".
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

	if (rtt_map_irq_pending()) {
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

		if (rtt_map_irq_pending()) {
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
 *   1. If enabled, sample ISR_EL1; on a pending physical IRQ return true
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

		if (rtt_map_irq_pending()) {
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
/*
 * Build the constant per-call attribute bits of the host_s2tte from
 * @memattr and @s2ap. The PA is OR'd in per-entry by
 * unprot_map_one_entry().
 *
 * Returns RMI_SUCCESS with @base_attrs_out populated, or RMI_ERROR_INPUT
 * if the indirect base permission index is out of range.
 */
static unsigned long build_unprot_map_attrs(struct s2tt_context *s2_ctx,
					    unsigned long memattr,
					    unsigned long s2ap,
					    unsigned long *base_attrs_out)
{
	unsigned long attrs = INPLACE(S2TTE_MEMATTR, memattr);

	if (s2_ctx->indirect_s2ap) {
		/* Indirect encoding: @s2ap is the PI_INDEX value. */
		attrs = s2tte_set_pi_index(s2_ctx, attrs, s2ap);
		if (s2tte_get_pi_index(s2_ctx, attrs) >
				(unsigned long)S2AP_IND_BASE_PERM_IDX_RW) {
			return RMI_ERROR_INPUT;
		}
	} else {
		/* Direct encoding: @s2ap bits encode R/W permissions. */
		unsigned long defined = MASK(RMI_S2AP_DIRECT_READ) |
					MASK(RMI_S2AP_DIRECT_WRITE);

		/* Upper s2ap bits in the flags field are SBZ. */
		if ((s2ap & ~defined) != 0UL) {
			return RMI_ERROR_INPUT;
		}
		if ((s2ap & MASK(RMI_S2AP_DIRECT_READ)) != 0UL) {
			attrs |= INPLACE(S2TTE_PERM_R, 1UL);
		}
		if ((s2ap & MASK(RMI_S2AP_DIRECT_WRITE)) != 0UL) {
			attrs |= INPLACE(S2TTE_PERM_W, 1UL);
		}
	}

	*base_attrs_out = attrs;
	return RMI_SUCCESS;
}


/*
 * Validate inputs to RMI_RTT_UNPROT_MAP. Thin wrapper around
 * validate_map_inputs_common() that decodes RmiRttUnprotMapFlags
 * (OADDR_TYPE / LIST_COUNT / MEMATTR / S2AP), then builds the constant
 * per-call attribute mask in @base_attrs_out for the walk loop to OR
 * with each per-entry PA. Descriptors must carry RMI_OP_MEM_UNDELEGATED
 * and the range must lie outside PAR.
 */
static unsigned long validate_unprot_map_inputs(unsigned long base,
						unsigned long top,
						unsigned long flags,
						unsigned long oaddr,
						struct rd *rd,
						struct addr_list *list_out,
						long *level_out,
						unsigned long *map_size_out,
						unsigned long *base_attrs_out)
{
	struct s2tt_context s2_ctx = rd->s2_ctx[PRIMARY_S2_CTX_ID];
	unsigned long oaddr_type;
	unsigned long list_count;
	unsigned long memattr;
	unsigned long s2ap;
	unsigned long ret;

	oaddr_type = EXTRACT(RMI_RTT_UNPROT_MAP_FLAGS_OADDR_TYPE, flags);
	list_count = EXTRACT(RMI_RTT_UNPROT_MAP_FLAGS_LIST_COUNT, flags);
	memattr = EXTRACT(RMI_RTT_UNPROT_MAP_FLAGS_MEMATTR, flags);
	s2ap = EXTRACT(RMI_RTT_UNPROT_MAP_FLAGS_S2AP, flags);

	ret = validate_map_inputs_common(base, top, oaddr_type, list_count,
					 oaddr, rd,
					 RMI_OP_MEM_UNDELEGATED,
					 /* must_be_in_par= */ false,
					 list_out, level_out, map_size_out);
	if (ret != RMI_SUCCESS) {
		return ret;
	}

	return build_unprot_map_attrs(&s2_ctx, memattr, s2ap, base_attrs_out);
}

/*
 * Map one NS block at @pa into the leaf RTT slot &s2tt[index]
 * (already locked and mapped) at level @level. The OA encoding takes
 * @base_attrs as the constant memattr + AP mask built once by the
 * validator and OR'd here with the per-entry PA.
 *
 * Unlike data_map there is no deferred drain: the leaf s2tte write is
 * the only architectural side effect, so the entry returns its final
 * status directly.
 *
 * Returns:
 *   RMI_SUCCESS                                slot now maps @pa
 *                                              (or already did, idempotent).
 *   RMI_ERROR_INPUT                            host_s2tte is invalid for
 *                                              @level.
 *   pack_return_code(RMI_ERROR_RTT, level)     slot already drained-pending,
 *                                              non-NS, or assigned to a
 *                                              different PA / encoding.
 */
static unsigned long unprot_map_one_entry(struct s2tt_context *s2_ctx,
					  unsigned long *s2tt,
					  unsigned long index,
					  unsigned long pa,
					  long level,
					  unsigned long base_attrs)
{
	unsigned long host_s2tte;
	unsigned long s2tte;
	unsigned long new_s2tte;

	host_s2tte = pa_to_s2tte(s2_ctx, pa) | base_attrs;
	if (!host_ns_s2tte_is_valid(s2_ctx, host_s2tte, level)) {
		return RMI_ERROR_INPUT;
	}

	s2tte = s2tte_read(&s2tt[index]);

	/*
	 * If the slot is still carrying a deferred-drain marker stamped
	 * by an in-flight RMI_RTT_UNPROT_UNMAP, the stage-2 TLB has not
	 * yet been invalidated for the previous NS PA. Refuse the remap
	 * until that SRO's drain has cleared the marker, otherwise a
	 * stale translation could resolve to the old PA after the realm
	 * starts using the new mapping.
	 */
	if (s2tte_drain_pending(s2tte)) {
		return pack_return_code(RMI_ERROR_RTT, (unsigned char)level);
	}

	new_s2tte = s2tte_create_assigned_ns(s2_ctx, host_s2tte, level, 0UL);

	if (!s2tte_is_unassigned_ns(s2_ctx, s2tte)) {
		/*
		 * Idempotent: if already mapped NS with the same encoding
		 * report success without rewriting the slot.
		 */
		if (s2tte_is_assigned_ns(s2_ctx, s2tte, level) &&
		    (s2tte == new_s2tte)) {
			return RMI_SUCCESS;
		}
		return pack_return_code(RMI_ERROR_RTT, (unsigned char)level);
	}

	s2tte_write(&s2tt[index], new_s2tte);
	return RMI_SUCCESS;
}

/*
 * Implements SMC_RMI_RTT_UNPROT_MAP with range support over a single
 * leaf RTT (one tree, one iteration). Mirrors smc_rtt_data_map() in
 * structure but maps NS memory into the unprotected IPA space and has
 * no per-block drain phase: each block is a single architectural
 * leaf-s2tte write, so the only yield point is the head-of-loop IRQ
 * check between blocks. Partial progress is reported as RMI_SUCCESS
 * with @out_top so the host resumes from the unmapped tail.
 *
 * We don't hold a reference on the NS granule when it is mapped into
 * a realm. Instead we rely on the guarantees provided by the
 * architecture to ensure that an NS access to a protected granule is
 * prohibited even within the realm.
 *
 * @flags layout is RmiRttUnprotMapFlags: OADDR_TYPE selects SINGLE
 * (one descriptor in @oaddr) or LIST (LIST_COUNT descriptors at the
 * NS PA @oaddr); MEMATTR and S2AP are constant for the call and
 * compose the per-entry host_s2tte together with the per-descriptor
 * PA. The walk level is taken from the SZ field of the first
 * descriptor; a later descriptor at a different level stops the
 * iteration.
 *
 * Output:
 *   x[0] = RMI_SUCCESS | RMI_ERROR_*
 *   x[1] = out_top (IPA past the last successfully mapped block)
 *
 * No SRO lifecycle: every block completes synchronously with a single
 * leaf s2tte write, so there is nothing for a continue handler to
 * resume. Yield on IRQ is reported as partial progress, not as an
 * RMI_INCOMPLETE handle.
 */
void smc_rtt_unprot_map(unsigned long rd_addr,
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
	unsigned long base_attrs;
	unsigned long idx;
	long level;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	ret = validate_unprot_map_inputs(base, top, flags, oaddr, rd,
					 &list, &level, &map_size,
					 &base_attrs);
	if (ret != RMI_SUCCESS) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		res->x[0] = ret;
		return;
	}

	s2_ctx = rd->s2_ctx[PRIMARY_S2_CTX_ID];

	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);

	/*
	 * Root RTT now locked. The remainder of the call uses only the
	 * stack copy of the primary S2 context.
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
	 * alignment). Stop and return progress on any per-block error or
	 * on unprot_map_one_entry() failure.
	 *
	 * @idx is the loop cursor; @wi.index is left at the walk's
	 * landing slot.
	 */
	for (idx = wi.index; idx < S2TTES_PER_S2TT; idx++) {
		unsigned long pa = 0UL;
		bool yield;

		ret = map_pop_next_block(&list, &s2_ctx,
					 RMI_OP_MEM_UNDELEGATED,
					 level, map_size, out_top, top,
					 &pa, &yield);
		if (yield || (ret != RMI_SUCCESS)) {
			goto done;
		}

		ret = unprot_map_one_entry(&s2_ctx, s2tt, idx, pa, level,
					   base_attrs);
		if (ret != RMI_SUCCESS) {
			goto done;
		}

		out_top += map_size;
	}

done:
	ret = map_partial_progress_finalize(res, ret, out_top, base);

	buffer_unmap(s2tt);
out_unlock_llt:
	granule_unlock(wi.g_llt);
	res->x[0] = ret;
}

/*
 * Returns true if the block [@pa, @pa + @block_size) is fully contained
 * in one of the VDEV's @n_ranges address ranges. Each addr_range is
 * half-open [base, top).
 */
static bool block_in_vdev_range(const struct rmi_address_range *ranges,
				unsigned long n_ranges,
				unsigned long pa,
				unsigned long block_size)
{
	unsigned long block_end = pa + block_size;

	for (unsigned long i = 0UL; i < n_ranges; i++) {
		if ((pa >= ranges[i].base) && (block_end <= ranges[i].top)) {
			return true;
		}
	}
	return false;
}

/*
 * Validate inputs to RMI_RTT_DEV_MAP. Thin wrapper around
 * validate_map_inputs_common() that decodes RmiRttProtMapFlags
 * (OADDR_TYPE / LIST_COUNT). Descriptors must carry
 * RMI_OP_MEM_DELEGATED and the range must lie inside PAR.
 */
static unsigned long validate_dev_map_inputs(unsigned long base,
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
 * Roll back a drain-time failure after the leaf slot has been stamped.
 * Every dev_granule below @ctx->pending_off was transitioned to MAPPED
 * by this SRO. Walk the cursor backwards, returning each dev_granule
 * to DELEGATED. On a pending IRQ leave @ctx->pending_off pointing to
 * the remaining rollback span and return with *@yielded set so
 * RMI_OP_CONTINUE can resume. Once the cursor reaches zero, clear the
 * leaf marker, drop the refcount taken when the marker was stamped,
 * and return @ctx->ret_err.
 *
 * Caller contract: @ctx->g_llt is locked and @s2tt is its mapping.
 */
static unsigned long dev_map_rollback_pending(struct sro_map_ctx *ctx,
					      unsigned long *s2tt,
					      bool *yielded)
{
	unsigned long stamped;

	*yielded = false;

	while (ctx->pending_off > 0UL) {
		struct dev_granule *g_dev;
		enum dev_coh_type type;

		if (rtt_map_irq_pending()) {
			*yielded = true;
			return RMI_SUCCESS;
		}

		ctx->pending_off -= GRANULE_SIZE;

		g_dev = find_lock_dev_granule(ctx->pa + ctx->pending_off,
					      DEV_GRANULE_STATE_MAPPED,
					      &type);
		if (g_dev != NULL) {
			dev_granule_unlock_transition(g_dev,
						      DEV_GRANULE_STATE_DELEGATED);
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
 * Yieldable per-granule drain for an in-flight RMI_RTT_DEV_MAP block,
 * plus the finalize of the leaf s2tte on drain completion. Resumes
 * from @ctx->pending_off and advances it past every granule it has
 * transitioned. Each iteration:
 *
 *   1. If enabled, sample ISR_EL1; on a pending physical IRQ return true
 *      with the cursor pointing at the next pending granule.
 *   2. find_lock_dev_granule(pa, DELEGATED, &type). On failure switch
 *      to rollback. Rollback is also yieldable; when complete it
 *      clears the leaf marker and returns RMI_ERROR_INPUT.
 *   3. On the first iteration (pending_off == 0), pin @ctx->coh_type
 *      to the type just locked. On subsequent iterations reject any
 *      mismatch with yieldable rollback + RMI_ERROR_INPUT so the
 *      entire block stays in one dev memory region.
 *   4. dev_granule_unlock_transition(g, MAPPED).
 *
 * On drain completion the leaf s2tte at &s2tt[@ctx->index] is rewritten
 * from the drain-pending marker to the assigned form for @ctx->pa,
 * preserving RIPAS / dev attrs from the still-stamped s2tte.
 *
 * Caller contract: the leaf RTT granule (@ctx->g_llt) is locked and
 * @s2tt is its mapping for the duration of the call. Called from both
 * dev_map_one_entry (entry path) and dev_map_continue_handler (continue
 * path); both arrange the lock+map before invoking.
 *
 * Returns RMI_SUCCESS with *@yielded set on IRQ-yield during drain or
 * rollback, RMI_SUCCESS with *@yielded clear when the cursor reaches
 * the block size for @ctx->level (drain complete, s2tte finalized), or
 * RMI_ERROR_INPUT if a backing granule cannot be claimed or has a
 * mismatching coh_type and rollback has completed.
 */
static unsigned long dev_map_drain_pending(struct sro_map_ctx *ctx,
					   const struct s2tt_context *s2_ctx,
					   unsigned long *s2tt,
					   bool *yielded)
{
	unsigned long map_size = s2tte_map_size(ctx->level);
	unsigned long stamped, new_s2tte;

	*yielded = false;

	if (ctx->rollback) {
		return dev_map_rollback_pending(ctx, s2tt, yielded);
	}

	while (ctx->pending_off < map_size) {
		struct dev_granule *g_dev;
		enum dev_coh_type type;

		if (rtt_map_irq_pending()) {
			*yielded = true;
			return RMI_SUCCESS;
		}

		g_dev = find_lock_dev_granule(ctx->pa + ctx->pending_off,
					      DEV_GRANULE_STATE_DELEGATED,
					      &type);
		if (g_dev == NULL) {
			ctx->rollback = true;
			ctx->ret_err = RMI_ERROR_INPUT;
			return dev_map_rollback_pending(ctx, s2tt, yielded);
		}

		if (ctx->pending_off == 0UL) {
			ctx->coh_type = type;
		} else if (type != ctx->coh_type) {
			dev_granule_unlock(g_dev);
			ctx->rollback = true;
			ctx->ret_err = RMI_ERROR_INPUT;
			return dev_map_rollback_pending(ctx, s2tt, yielded);
		}

		dev_granule_unlock_transition(g_dev, DEV_GRANULE_STATE_MAPPED);

		ctx->pending_off += GRANULE_SIZE;
	}

	stamped = s2tte_read(&s2tt[ctx->index]);
	assert(s2tte_drain_pending(stamped));
	assert(s2tte_drain_handle(stamped) == sro_ctx_my_handle());

	new_s2tte = s2tte_create_assigned_dev_unchanged(s2_ctx,
				s2tte_clear_drain_pending(stamped),
				ctx->pa, ctx->level);
	s2tte_write(&s2tt[ctx->index], new_s2tte);

	return RMI_SUCCESS;
}

/*
 * Prepare one block of DELEGATED device memory at @pa for mapping into
 * the leaf RTT slot &s2tt[index] (already locked and mapped) at level
 * @level. The block covers s2tte_map_size(@level) bytes and is backed
 * by map_size / GRANULE_SIZE consecutive dev_granules starting at @pa.
 *
 * This function performs only the prepare phase (validate + stamp the
 * leaf s2tte with the drain-pending marker carrying the current SRO
 * handle + take one refcount on @g_llt). The actual dev_granule lock /
 * state-transition work is run by dev_map_drain_pending() one granule
 * at a time so the call can yield to pending IRQs between granules.
 *
 * Returns:
 *   RMI_SUCCESS      slot prepared. The caller must populate the SRO
 *                    ctx and invoke dev_map_drain_pending().
 *   pack_return_code(RMI_ERROR_RTT, level)
 *                    slot is not unassigned (empty / destroyed).
 *   RMI_BUSY         slot still owes deferred maintenance from a
 *                    previous SRO (concurrent unmap drain in flight).
 */
static unsigned long dev_map_one_entry(struct s2tt_context *s2_ctx,
				       unsigned long *s2tt,
				       unsigned long index,
				       struct granule *g_llt,
				       long level)
{
	unsigned long s2tte, stamped;

	s2tte = s2tte_read(&s2tt[index]);
	if (!(s2tte_is_unassigned_empty(s2_ctx, s2tte) ||
	      s2tte_is_unassigned_destroyed(s2_ctx, s2tte))) {
		return pack_return_code(RMI_ERROR_RTT, (unsigned char)level);
	}
	if (s2tte_drain_pending(s2tte)) {
		return RMI_BUSY;
	}

	stamped = s2tte_set_drain_pending(s2tte, sro_ctx_my_handle());
	s2tte_write(&s2tt[index], stamped);
	atomic_granule_get(g_llt);

	return RMI_SUCCESS;
}

/*
 * Implements SMC_RMI_RTT_DEV_MAP with range support over a single leaf
 * RTT (one tree, one iteration). Mirrors smc_rtt_data_map() in
 * structure: per-block work stamps the leaf with a drain-pending
 * marker, then a yieldable drain locks each backing dev_granule one at
 * a time and transitions DELEGATED -> MAPPED. On an IRQ-yield
 * mid-drain the call seals an SRO context and returns RMI_INCOMPLETE
 * so the host can resume via RMI_OP_CONTINUE.
 *
 * The walk level is taken from the SZ field of the first descriptor;
 * supported levels are L1/L2 blocks and L3 pages. A later descriptor
 * at a different level stops the iteration.
 *
 * @flags encodes RmiRttProtMapFlags: OADDR_TYPE selects SINGLE / LIST,
 * LIST_COUNT is the descriptor count for LIST.
 *
 * Output on terminal progress:
 *   x[0] = RMI_SUCCESS | RMI_ERROR_*
 *   x[1] = out_top (IPA past the last successfully mapped block)
 *
 * Output on yield (drain of one block in flight):
 *   x[0] = RMI_INCOMPLETE | RMI_OP_MEM_REQ_NONE | RMI_OP_CANNOT_CANCEL
 *   x[1] = SRO context handle (pass to RMI_OP_CONTINUE).
 */
void smc_rtt_dev_map(unsigned long rd_addr,
		     unsigned long vdev_addr,
		     unsigned long base,
		     unsigned long top,
		     unsigned long flags,
		     unsigned long oaddr,
		     struct smc_result *res)
{
	struct addr_list list;
	struct granule *g_rd = NULL;
	struct granule *g_vdev;
	struct rd *rd;
	struct vdev *vd;
	struct s2tt_walk wi;
	struct s2tt_context s2_ctx;
	struct rmi_address_range vdev_ranges[RMI_VDEV_PARAMS_ADDR_RANGE_MAX];
	unsigned long n_vdev_ranges;
	unsigned long *s2tt = NULL;
	unsigned long out_top = base;
	unsigned long ret;
	unsigned long map_size;
	unsigned long idx;
	long level;
	bool yielded = false;

	/* Reserve an SRO context up front. */
	ret = sro_ctx_reserve(SMC_RMI_RTT_DEV_MAP, 0UL, false, false,
			      SMC_RMI_OP_CONTINUE);
	if (ret != RMI_SUCCESS) {
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

	ret = validate_dev_map_inputs(base, top, flags, oaddr, rd,
				      &list, &level, &map_size);
	if (ret != RMI_SUCCESS) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		goto out_release_sro;
	}

	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		ret = RMI_ERROR_INPUT;
		buffer_unmap(rd);
		granule_unlock(g_rd);
		goto out_release_sro;
	}

	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if (vd->g_rd != g_rd) {
		ret = RMI_ERROR_INPUT;
		buffer_unmap(vd);
		granule_unlock(g_vdev);
		buffer_unmap(rd);
		granule_unlock(g_rd);
		goto out_release_sro;
	}

	/*
	 * Snapshot the VDEV's address ranges so we can release the
	 * VDEV slot before holding the leaf RTT mapping.
	 */
	n_vdev_ranges = vd->num_addr_range;
	for (unsigned long i = 0UL; i < n_vdev_ranges; i++) {
		vdev_ranges[i] = vd->addr_range[i];
	}
	buffer_unmap(vd);
	granule_unlock(g_vdev);

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

	for (idx = wi.index; idx < S2TTES_PER_S2TT; idx++) {
		struct sro_map_ctx *ctx;
		unsigned long pa = 0UL;
		bool yield;

		ret = map_pop_next_block(&list, &s2_ctx,
					 RMI_OP_MEM_DELEGATED,
					 level, map_size, out_top, top,
					 &pa, &yield);
		if (yield || (ret != RMI_SUCCESS)) {
			goto done;
		}

		if (!block_in_vdev_range(vdev_ranges, n_vdev_ranges,
					 pa, map_size)) {
			ret = RMI_ERROR_INPUT;
			goto done;
		}

		ret = dev_map_one_entry(&s2_ctx, s2tt, idx, wi.g_llt, level);
		if (ret != RMI_SUCCESS) {
			goto done;
		}

		ctx = &my_sro_ctx()->map_ctx;
		sro_map_ctx_init(ctx, wi.g_llt, rd_addr, pa,
				 out_top, base, idx, level);

		ret = dev_map_drain_pending(ctx, &s2_ctx, s2tt, &yielded);
		if (ret != RMI_SUCCESS) {
			goto done;
		}
		if (yielded) {
			goto done;
		}

		out_top += map_size;
	}

done:
	if (!yielded) {
		ret = map_partial_progress_finalize(res, ret, out_top, base);
	}

	buffer_unmap(s2tt);
out_unlock_llt:
	granule_unlock(wi.g_llt);
out_release_sro:
	if (yielded) {
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
 * SRO continue callback for RMI_RTT_DEV_MAP. Resumes the per-granule
 * drain started by smc_rtt_dev_map() and, when complete, finalizes the
 * leaf s2tte to assigned_dev_unchanged.
 *
 * The RD granule is locked before the leaf RTT to preserve the normal
 * RD -> RTT lock order. The extra refcount taken at stamp time pins
 * the leaf RTT across the yield.
 *
 * Output on completion:
 *   x[0] = RMI_SUCCESS
 *   x[1] = IPA past the now-mapped block
 *
 * Output on further yield:
 *   x[0] = RMI_INCOMPLETE | RMI_OP_MEM_REQ_NONE | RMI_OP_CANNOT_CANCEL
 *   x[1] = 0
 */
void dev_map_continue_handler(unsigned long fid,
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
	assert(sro->init_command == SMC_RMI_RTT_DEV_MAP);
	(void)fid;

	ctx = &sro->map_ctx;
	assert(ctx->g_llt != NULL);

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

	ret = dev_map_drain_pending(ctx, &s2_ctx, s2tt, &yielded);

	buffer_unmap(s2tt);
	granule_unlock(ctx->g_llt);

	if (ret != RMI_SUCCESS) {
		res->x[0] = map_partial_progress_finalize(res, ret,
							  ctx->ipa,
							  ctx->init_base);
		ctx->g_llt = NULL;
		return;
	}

	if (yielded) {
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

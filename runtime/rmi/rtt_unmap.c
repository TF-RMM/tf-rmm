/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <addr_list.h>
#include <arch_helpers.h>
#include <assert.h>
#include <buffer.h>
#include <debug.h>
#include <dev_granule.h>
#include <granule.h>
#include <planes.h>
#include <realm.h>
#include <ripas.h>
#include <rtt_internal.h>
#include <s2tt.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <smmuv3.h>
#include <sro_context.h>
#include <status.h>
#include <stddef.h>
#include <tracking_region.h>
#include <xlat_low_va.h>

/*
 * Validate inputs to RMI_RTT_DATA_UNMAP / RMI_RTT_UNPROT_UNMAP /
 * RMI_RTT_DEV_UNMAP.
 *
 * Checks (in order):
 *   - flags.oaddr_type must be one of NONE / SINGLE / LIST,
 *   - base and top must be granule-aligned and base < top,
 *   - base and (top - GRANULE_SIZE) must lie within the realm's IPA space,
 *   - [base, top) must lie inside the realm's PAR (data unmap, @in_par)
 *     or strictly outside it (unprot unmap, !@in_par),
 *   - for NONE / SINGLE: oaddr is SBZ and flags.list_count is zero,
 *   - for LIST: oaddr must be unsigned-long-aligned and reference an NS
 *     granule, and flags.list_count must be non-zero.
 *
 * On success @oaddr_type_out is set to the extracted oaddr_type and
 * @list_count_out is set to the effective upper bound for the address list:
 *   - 0 for NONE and SINGLE,
 *   - for LIST, min(flags.list_count, ADDR_LIST_MAX_RANGES, descriptor
 *     slots remaining between @oaddr and the end of its NS granule).
 *     @oaddr is not required to be GRANULE_ALIGNED, so the buffer is
 *     clipped at the granule boundary.
 *
 * The required base/top alignment to the level at which the walk lands is
 * checked separately, after the walk.
 *
 * Returns RMI_SUCCESS on valid input or RMI_ERROR_INPUT otherwise.
 */
static unsigned long validate_unmap_inputs(unsigned long base,
					   unsigned long top,
					   unsigned long flags,
					   unsigned long oaddr,
					   struct rd *rd,
					   bool in_par,
					   unsigned long *oaddr_type_out,
					   unsigned long *list_count_out)
{
	unsigned long oaddr_type = EXTRACT(RMI_RTT_UNMAP_FLAGS_OADDR_TYPE,
					   flags);
	unsigned long list_count = EXTRACT(RMI_RTT_UNMAP_FLAGS_LIST_COUNT,
					   flags);

	if (!GRANULE_ALIGNED(base) || !GRANULE_ALIGNED(top) ||
	    (top <= base)) {
		return RMI_ERROR_INPUT;
	}

	if (!validate_map_addr(base, S2TT_PAGE_LEVEL, rd) ||
	    !validate_map_addr(top - GRANULE_SIZE, S2TT_PAGE_LEVEL, rd)) {
		return RMI_ERROR_INPUT;
	}

	if (in_par) {
		if (!addr_in_par(rd, base) ||
		    !addr_in_par(rd, top - GRANULE_SIZE)) {
			return RMI_ERROR_INPUT;
		}
	} else {
		if (addr_in_par(rd, base) ||
		    addr_in_par(rd, top - GRANULE_SIZE)) {
			return RMI_ERROR_INPUT;
		}
	}

	switch (oaddr_type) {
	case RMI_ADDR_TYPE_NONE:
	case RMI_ADDR_TYPE_SINGLE:
		/* list_count and oaddr are SBZ for non-LIST types */
		if ((oaddr != 0UL) || (list_count != 0UL)) {
			return RMI_ERROR_INPUT;
		}
		break;
	case RMI_ADDR_TYPE_LIST: {
		unsigned long offset_slots;
		unsigned long granule_remaining;

		if (list_count == 0UL) {
			return RMI_ERROR_INPUT;
		}
		if (!ALIGNED(oaddr, sizeof(unsigned long))) {
			return RMI_ERROR_INPUT;
		}
		/*
		 * The host buffer cannot cross a granule. Clip @list_count
		 * to the descriptor slots that fit between @oaddr and the
		 * end of its granule, and to the internal addr_list capacity.
		 */
		offset_slots = (oaddr & ~GRANULE_MASK) /
				sizeof(unsigned long);
		granule_remaining = ADDR_LIST_MAX_RANGES - offset_slots;
		/*
		 * oaddr & ~GRANULE_MASK is in [0, GRANULE_SIZE), so offset_slots is
		 * in [0, ADDR_LIST_MAX_RANGES) and granule_remaining is always >= 1.
		 */
		assert(granule_remaining > 0UL);
		list_count = MIN(list_count,
				 (unsigned long)ADDR_LIST_MAX_RANGES);
		list_count = MIN(list_count, granule_remaining);
		break;
	}
	default:
		return RMI_ERROR_INPUT;
	}

	*oaddr_type_out = oaddr_type;
	*list_count_out = list_count;
	return RMI_SUCCESS;
}

/*
 * Reason returned by rtt_unmap_one_table().
 */
enum data_unmap_step {
	DATA_UNMAP_STEP_DONE,		/* stop condition reached; success */
	DATA_UNMAP_STEP_ERROR,		/* res->x[] populated with an error */
};

/*
 * Flavor of the RMI_RTT_*UNMAP sweep currently in flight. Selected per
 * SRO context from init_command. Controls which live s2tte states are
 * accepted, what the unassigned replacement looks like, which backing
 * granule kind the drain transitions, and whether the sweep takes a
 * transient leaf-RTT refcount per stamped entry.
 *
 *   - DATA:   conventional Realm data. Accepts assigned_ram/empty/
 *             destroyed; drain transitions DATA granules back to
 *             DELEGATED with cache maintenance; leaf-RTT refcount is
 *             inherited from data_create().
 *   - UNPROT: NS mapping. Accepts assigned_ns; no granule drain;
 *             sweep takes a transient leaf-RTT refcount per stamped
 *             entry to match the DATA per-entry pin.
 *   - DEV:    Device memory. Accepts assigned_dev_dev/empty/destroyed;
 *             drain transitions dev_granules from MAPPED to DELEGATED;
 *             leaf-RTT refcount is inherited from dev_map.
 */
enum rtt_unmap_flavor {
	RTT_UNMAP_FLAVOR_DATA,
	RTT_UNMAP_FLAVOR_UNPROT,
	RTT_UNMAP_FLAVOR_DEV,
};

static enum rtt_unmap_flavor rtt_unmap_flavor_from_fid(unsigned long fid)
{
	switch (fid) {
	case SMC_RMI_RTT_DATA_UNMAP:
		return RTT_UNMAP_FLAVOR_DATA;
	case SMC_RMI_RTT_UNPROT_UNMAP:
		return RTT_UNMAP_FLAVOR_UNPROT;
	case SMC_RMI_RTT_DEV_UNMAP:
		return RTT_UNMAP_FLAVOR_DEV;
	default:
		assert(false);
		return RTT_UNMAP_FLAVOR_DATA;
	}
}

static bool rtt_unmap_irq_pending(void)
{
#ifdef RMM_RTT_MAP_UNMAP_CHECK_ISR_EL1
	return (read_isr_el1() != 0UL);
#else
	return false;
#endif
}

/*
 * Return whether @s2tte represents conventional data for DATA_UNMAP.
 *
 * Device mappings must be rejected before looking up conventional backing
 * granules. On failure, populate @res with the RTT error required for a
 * mapping owned by the device-unmap command.
 */
static bool data_unmap_flavor_valid(struct s2tt_context *s2_ctx,
				    unsigned long s2tte, long level,
				    struct smc_result *res)
{
	if (s2tte_is_assigned_dev(s2_ctx, s2tte) ||
	    s2tte_is_assigned_dev_dev(s2_ctx, s2tte, level)) {
		res->x[0] = pack_return_code_level(RMI_ERROR_RTT,
					     (unsigned char)level);
		res->x[1] = 0UL;
		return false;
	}

	return true;
}

/* Validation retains one coarse lock until the sweep claims it or stops. */
struct rtt_unmap_coarse_lock {
	struct granule *data;
	struct dev_granule *dev;
};

/* Release a validated coarse unit that was not claimed by the sweep. */
static void rtt_unmap_coarse_unlock(struct rtt_unmap_coarse_lock *coarse)
{
	if (coarse->data != NULL) {
		granule_unlock(coarse->data);
		coarse->data = NULL;
	}
	if (coarse->dev != NULL) {
		dev_granule_unlock(coarse->dev);
		coarse->dev = NULL;
	}
}

/*
 * Claim a queued coarse unit for @ctx before any deferred work can yield.
 * The leaf is locked and its S2TTE carries this SRO's drain-pending marker.
 * Transfer the validated, locked source to PARTIAL ownership and unlock it;
 * @ctx keeps that ownership until the whole unit can become DELEGATED.
 */
static void rtt_unmap_coarse_claim(struct sro_unmap_ctx *ctx,
				 struct rtt_unmap_coarse_lock *coarse)
{
	assert((ctx->g_coarse == NULL) && (ctx->g_coarse_dev == NULL));
	assert((coarse->data == NULL) || (coarse->dev == NULL));
	if (coarse->data != NULL) {
		ctx->g_coarse = coarse->data;
		coarse->data = NULL;
		granule_unlock_transition(ctx->g_coarse, GRANULE_STATE_PARTIAL);
	} else if (coarse->dev != NULL) {
		ctx->g_coarse_dev = coarse->dev;
		coarse->dev = NULL;
		dev_granule_unlock_transition(ctx->g_coarse_dev, DEV_GRANULE_STATE_PARTIAL);
	}
}

/*
 * Validate the DATA/MAPPED granules covering one S2TT block and reject any
 * auxiliary references before removing its primary mapping. The leaf is locked.
 * Return an encoded lookup/tracking/auxiliary error, or RMI_SUCCESS.
 *
 * Fine DATA/MAPPED states prevent SET_TRACKING from accepting a transition, so
 * fine locks can be released after validation. A coarse DATA/MAPPED granule
 * can transition to fine: retain its lock in @coarse until the caller has
 * queued the block and claimed it as PARTIAL. If the block cannot be queued,
 * the caller must release this lock without changing its state.
 */
static unsigned long rtt_unmap_tracking_validate(
					unsigned long pa,
					unsigned long map_size,
					enum rtt_unmap_flavor flavor,
					struct rtt_unmap_coarse_lock *coarse)
{
	unsigned long offset = 0UL;

	assert((coarse->data == NULL) && (coarse->dev == NULL));
	assert(flavor != RTT_UNMAP_FLAVOR_UNPROT);
	while (offset < map_size) {
		struct granule *g = NULL;
		struct dev_granule *g_dev = NULL;
		enum dev_coh_type type;
		unsigned long addr = pa + offset;
		unsigned long tracking_size;
		unsigned long ret;
		bool has_aux;

		if (flavor == RTT_UNMAP_FLAVOR_DATA) {
			ret = tr_find_lock_active_granule(addr, GRANULE_STATE_DATA,
							&g, &tracking_size);
		} else {
			ret = tr_find_lock_active_dev_granule(addr, DEV_GRANULE_STATE_MAPPED,
							&g_dev, &type, &tracking_size);
		}
		if (ret != RMI_SUCCESS) {
			return ret;
		}
		has_aux = (g != NULL) ? (granule_refcount_read_acquire(g) != 0U) :
				       (dev_granule_refcount_read_acquire(g_dev) != 0U);
		if ((tracking_size > (map_size - offset)) || !ALIGNED(addr, tracking_size)) {
			ret = pack_return_code_level_addr(RMI_ERROR_TRACKING, 0U, addr);
		} else if (has_aux) {
			ret = pack_return_code_level(RMI_ERROR_RTT_AUX, 0U);
		}
		if ((ret == RMI_SUCCESS) && (tracking_size == tracking_region_get_size())) {
			coarse->data = g;
			coarse->dev = g_dev;
		} else if (g != NULL) {
			granule_unlock(g);
		} else {
			dev_granule_unlock(g_dev);
		}
		if (ret != RMI_SUCCESS) {
			return ret;
		}
		offset += tracking_size;
	}
	return RMI_SUCCESS;
}

/*
 * Compute the unassigned s2tte that replaces a freed live entry, and
 * indicate whether the entry owed a TLBI (the HW-valid case).
 */
static unsigned long unmap_make_new_s2tte(struct s2tt_context *s2_ctx,
					  unsigned long s2tte, long level,
					  enum rtt_unmap_flavor flavor,
					  bool *tlbi_needed)
{
	unsigned long new_s2tte;

	switch (flavor) {
	case RTT_UNMAP_FLAVOR_DATA:
		if (s2tte_is_assigned_ram(s2_ctx, s2tte, level)) {
			new_s2tte = s2tte_create_unassigned_destroyed(
				s2_ctx,
				default_protected_ap(s2_ctx));
			*tlbi_needed = true;
		} else if (s2tte_is_assigned_empty(s2_ctx, s2tte, level)) {
			new_s2tte = s2tte_create_unassigned_empty(s2_ctx,
								  s2tte);
			*tlbi_needed = false;
		} else {
			assert(s2tte_is_assigned_destroyed(s2_ctx, s2tte,
							   level));
			new_s2tte = s2tte_create_unassigned_destroyed(s2_ctx,
								      s2tte);
			*tlbi_needed = false;
		}
		break;
	case RTT_UNMAP_FLAVOR_DEV:
		if (s2tte_is_assigned_dev_dev(s2_ctx, s2tte, level)) {
			new_s2tte = s2tte_create_unassigned_destroyed(s2_ctx,
								      s2tte);
			*tlbi_needed = true;
		} else if (s2tte_is_assigned_dev_empty(s2_ctx, s2tte,
						       level)) {
			new_s2tte = s2tte_create_unassigned_empty(s2_ctx,
								  s2tte);
			*tlbi_needed = false;
		} else {
			assert(s2tte_is_assigned_dev_destroyed(s2_ctx,
							       s2tte,
							       level));
			new_s2tte = s2tte_create_unassigned_destroyed(s2_ctx,
								      s2tte);
			*tlbi_needed = false;
		}
		break;
	default:
		assert(flavor == RTT_UNMAP_FLAVOR_UNPROT);
		assert(s2tte_is_assigned_ns(s2_ctx, s2tte, level));
		new_s2tte = s2tte_create_unassigned_ns(s2_ctx, UNUSED_UL);
		*tlbi_needed = true;
		break;
	}

	return new_s2tte;
}

/*
 * Sweep one leaf RTT for RMI_RTT_DATA_UNMAP, RMI_RTT_UNPROT_UNMAP, or
 * RMI_RTT_DEV_UNMAP, as selected by @flavor.
 *
 * Walks forward from entry @start_idx (covering IPA @start_addr),
 * mutating each live s2tte owned by the flavor to its unassigned form
 * and stamping the SW drain marker (plus the TLBI-pending bit when the
 * freed entry had a HW-valid mapping). The freed OA range is appended
 * to @out_list. This routine performs no cache maintenance and
 * therefore never yields.
 *
 * The flavor controls a few in-loop choices:
 *   - Which live state is owned (DATA: assigned_ram / assigned_empty /
 *     assigned_destroyed; UNPROT: assigned_ns; DEV: assigned_dev_dev /
 *     assigned_dev_empty / assigned_dev_destroyed); any other live
 *     state terminates the sweep (RMI_ERROR_RTT on the very first
 *     overall entry, otherwise stop with partial progress).
 *   - The auxiliary-RTT live-mapping check (DATA only).
 *   - The addr_list block status (DATA: RMI_OP_MEM_DELEGATED;
 *     UNPROT: RMI_OP_MEM_UNDELEGATED; DEV: RMI_OP_MEM_DELEGATED).
 *   - The unassigned descriptor written back (DATA and DEV preserve
 *     RIPAS via assigned_*-specific constructors; UNPROT writes
 *     unassigned_ns).
 *   - TLBI marker (DATA stamps it only for assigned_ram; DEV stamps it
 *     only for assigned_dev_dev; UNPROT stamps it on every stamped
 *     entry since assigned_ns is always HW-valid).
 *   - Per-entry leaf-RTT refcount: DATA inherits one from data_create(),
 *     DEV inherits one from dev_map(), and UNPROT takes a transient one
 *     here. The drops are deferred to the clear-marks phase of
 *     rtt_unmap_drain_and_clear() and emitted in one batch after the
 *     deferred TLBI and drain have fully completed on this leaf, so
 *     the still-held refcounts naturally pin the leaf (and
 *     transitively the RTT chain and RD) across any yield. The leaf
 *     address used by that phase is @ctx->g_llt, which the caller
 *     must set before invoking this routine.
 *
 * The sweep stops at the first of:
 *   - top (caller-supplied range end; each entry must fit fully),
 *   - end of the leaf table (S2TTES_PER_S2TT),
 *   - a DATA/DEV block outside the selected physical tracking region,
 *   - non-live entries, including drain-pending entries, are skipped,
 *   - a wrong-flavor live entry (DATA or DEV),
 *   - any entry that has live mappings in auxiliary RTTs (DATA only),
 *   - the output address list cannot describe the next block (SINGLE
 *     contiguity break or LIST_COUNT cap).
 *
 * On the very first iteration of the sweep (@idx == @start_idx),
 * any condition that would otherwise stop the sweep with SUCCESS
 * is reported as an error. After the sweep has
 * skipped one or more non-live entries (@idx advanced) the same
 * conditions instead stop with partial progress; the host reissues
 * from the live entry, where the condition then becomes a first-
 * iteration error.
 *
 * For DATA/DEV, validate each block under the leaf RTT lock. Fine DATA/MAPPED
 * states prevent transitions from being accepted. Retain a coarse granule
 * in @coarse until the block is queued, then claim it as PARTIAL and stop.
 * The SRO owns it across invalidation and drain, including yields. Unqueued
 * coarse units remain locked for the caller to release. Stay within one region.
 *
 * Returns DATA_UNMAP_STEP_ERROR when an error must be reported to the
 * host (res->x[] already populated). Otherwise returns
 * DATA_UNMAP_STEP_DONE. The sweep covers at most one leaf RTT; the
 * caller returns the updated @ctx->cur_base as out_top so the host can
 * reissue from there to cover later leaves.
 */
static enum data_unmap_step
rtt_unmap_one_table(struct s2tt_context *s2_ctx,
		    unsigned long *s2tt,
		    unsigned long start_idx,
		    unsigned long start_addr,
		    unsigned long top,
		    long level,
		    unsigned long map_size,
		    struct addr_list *out_list,
		    struct sro_unmap_ctx *ctx,
		    enum rtt_unmap_flavor flavor,
		    struct smc_result *res,
		    struct rtt_unmap_coarse_lock *coarse)
{
	unsigned long idx = start_idx;
	unsigned long addr = start_addr;
	unsigned long prev_pa = ~0UL;
	unsigned long blk_status = (flavor == RTT_UNMAP_FLAVOR_UNPROT) ?
					     RMI_OP_MEM_UNDELEGATED :
					     RMI_OP_MEM_DELEGATED;
	/*
	 * Sweep processes a single leaf table, so out_list is empty on
	 * entry. prev_pa starts as an invalid PA sentinel and is set after
	 * the first successful addr_list_add_block().
	 */
	while (idx < S2TTES_PER_S2TT) {
		unsigned long s2tte, pa;
		unsigned long new_s2tte = 0UL;
		bool tlbi_needed;

		s2tte = s2tte_read(&s2tt[idx]);

		/*
		 * Drain-pending entries are also non-live and architecturally
		 * unassigned, so they take the same skip path; the owning
		 * SRO still completes its deferred work.
		 */
		if (!s2tte_is_live(s2_ctx, s2tte, level)) {
			if ((addr + map_size) > top) {
				if (idx == start_idx) {
					res->x[0] = pack_return_code_level(
						RMI_ERROR_RTT,
						(unsigned char)level);
					res->x[1] = 0UL;
					return DATA_UNMAP_STEP_ERROR;
				}
				break;
			}
			idx++;
			addr += map_size;
			continue;
		}

		/*
		 * At non-leaf levels a live entry can be a TABLE
		 * descriptor. An unmap at @level cannot operate on
		 * such an entry: report only on the very first
		 * iteration of the sweep; otherwise stop with SUCCESS.
		 */
		if ((level < S2TT_PAGE_LEVEL) &&
		    s2tte_is_table(s2_ctx, s2tte, level)) {
			if (idx == start_idx) {
				res->x[0] = pack_return_code_level(
					RMI_ERROR_RTT,
					(unsigned char)level);
				res->x[1] = 0UL;
				return DATA_UNMAP_STEP_ERROR;
			}
			break;
		}

		/*
		 * Generic block-overflow check: a live entry whose
		 * block size exceeds the remaining requested range.
		 * Same first-iteration gating as the TABLE check
		 * above.
		 */
		if ((addr + map_size) > top) {
			if (idx == start_idx) {
				res->x[0] = pack_return_code_level(
					RMI_ERROR_RTT,
					(unsigned char)level);
				res->x[1] = 0UL;
				return DATA_UNMAP_STEP_ERROR;
			}
			break;
		}

		/*
		 * Validate the S2TTE flavor before selecting its backing-memory
		 * descriptor. A mapping owned by another unmap command must report
		 * an RTT error rather than a tracking lookup error.
		 */
		switch (flavor) {
		case RTT_UNMAP_FLAVOR_DATA:
			if (!data_unmap_flavor_valid(s2_ctx, s2tte, level, res)) {
				if (idx == start_idx) {
					return DATA_UNMAP_STEP_ERROR;
				}
				goto sweep_done;
			}
			break;
		case RTT_UNMAP_FLAVOR_DEV:
			if (!(s2tte_is_assigned_dev_dev(s2_ctx, s2tte,
							level) ||
			      s2tte_is_assigned_dev_empty(s2_ctx, s2tte,
							  level) ||
			      s2tte_is_assigned_dev_destroyed(s2_ctx, s2tte,
							      level))) {
				if (idx == start_idx) {
					res->x[0] = pack_return_code_level(
						RMI_ERROR_RTT,
						(unsigned char)level);
					res->x[1] = 0UL;
					return DATA_UNMAP_STEP_ERROR;
				}
				goto sweep_done;
			}
			break;
		case RTT_UNMAP_FLAVOR_UNPROT:
		default:
			assert(s2tte_is_assigned_ns(s2_ctx, s2tte, level));
			break;
		}

		pa = s2tte_pa(s2_ctx, s2tte, level);
		if (flavor != RTT_UNMAP_FLAVOR_UNPROT) {
			unsigned long ret;

			if (map_size > tracking_region_get_size()) {
				if (idx == start_idx) {
					res->x[0] = pack_return_code_level_addr(
							RMI_ERROR_TRACKING, 0U, pa);
					res->x[1] = 0UL;
					return DATA_UNMAP_STEP_ERROR;
				}
				break;
			}
			/*
			 * Keep the batch in one region: an owned coarse unit must be
			 * the only block in the deferred drain.
			 */
			if ((ctx->backing_addr != ~0UL) &&
			    (round_down(pa, tracking_region_get_size()) !=
			     round_down(ctx->backing_addr, tracking_region_get_size()))) {
				break;
			}
			ctx->backing_addr = pa;
			/* Retain the coarse lock until the queued block is claimed as PARTIAL. */
			ret = rtt_unmap_tracking_validate(pa, map_size, flavor, coarse);
			if (ret != RMI_SUCCESS) {
				if (idx == start_idx) {
					res->x[0] = ret;
					res->x[1] = 0UL;
					return DATA_UNMAP_STEP_ERROR;
				}
				break;
			}
		}

		/*
		 * Generic SINGLE PA-contiguity check: stop at the
		 * first PA discontinuity after the first overall
		 * entry; the host reissues with the returned cur_base
		 * to cover the next contiguous run.
		 */
		if ((ctx->oaddr_type == RMI_ADDR_TYPE_SINGLE) &&
		    (prev_pa != ~0UL) &&
		    (pa != (prev_pa + map_size))) {
			break;
		}

		if (!addr_list_add_block(out_list, pa, (int)level,
					 blk_status)) {
			break;
		}

		new_s2tte = unmap_make_new_s2tte(s2_ctx, s2tte, level,
						 flavor, &tlbi_needed);

		/*
		 * Stamp the SW drain-pending mark on every freed
		 * entry so concurrent map / RIPAS-set on the slot
		 * fails until our drain and the deferred clear pass
		 * have finished all deferred work for the old OA. The
		 * TLBI bit narrows the deferred invalidation pass to
		 * the entries that actually owe one.
		 */
		new_s2tte = s2tte_set_drain_pending(new_s2tte,
						    ctx->sro_handle);
		if (tlbi_needed) {
			new_s2tte = s2tte_set_tlbi_pending(new_s2tte);
		}
		s2tte_write(&s2tt[idx], new_s2tte);

		/*
		 * UNPROT: take a transient leaf-RTT refcount per
		 * stamped entry to mirror the long-lived ref DATA
		 * inherits from data_create() and DEV inherits from
		 * dev_map(). Both are dropped together by the
		 * clear-marks phase of rtt_unmap_drain_and_clear() in
		 * the deferred phase.
		 */
		if (flavor == RTT_UNMAP_FLAVOR_UNPROT) {
			atomic_granule_get(ctx->g_llt);
		}

		prev_pa = pa;
		idx++;
		addr += map_size;
		if ((coarse->data != NULL) || (coarse->dev != NULL)) {
			/* Claim the whole queued unit before invalidation or drain can yield. */
			rtt_unmap_coarse_claim(ctx, coarse);
			break;
		}
	}

sweep_done:
	ctx->cur_base = addr;
	return DATA_UNMAP_STEP_DONE;
}

/*
 * Drain the sole coarse unit owned by @ctx up to its exclusive @end, after
 * all invalidations complete. The caller holds the leaf lock and initializes
 * @pending_pa. PARTIAL ownership pins the backing representation while its
 * lock is released. DATA cache maintenance advances @pending_pa one page at
 * a time, doing at least one page per invocation before an IRQ yield.
 * Return true with ownership and progress retained on yield. Otherwise publish
 * the whole unit as DELEGATED, clear its owned pointer and return false.
 */
static bool rtt_unmap_drain_coarse(struct sro_unmap_ctx *ctx,
				 unsigned long end)
{
	assert(ALIGNED(ctx->backing_addr, tracking_region_get_size()));
	if (ctx->g_coarse != NULL) {
		assert(ctx->g_coarse_dev == NULL);
		while (ctx->pending_pa < end) {
			granule_dcci_poe_range(ctx->pending_pa, GRANULE_SIZE);
			ctx->pending_pa += GRANULE_SIZE;
			if ((ctx->pending_pa < end) && rtt_unmap_irq_pending()) {
				return true;
			}
		}
		/* No prefix becomes DELEGATED before the whole unit is maintained. */
		granule_lock(ctx->g_coarse, GRANULE_STATE_PARTIAL);
		granule_unlock_transition(ctx->g_coarse, GRANULE_STATE_DELEGATED);
		ctx->g_coarse = NULL;
	} else {
		assert(ctx->g_coarse_dev != NULL);
		dev_granule_lock(ctx->g_coarse_dev, DEV_GRANULE_STATE_PARTIAL);
		dev_granule_unlock_transition(ctx->g_coarse_dev, DEV_GRANULE_STATE_DELEGATED);
		ctx->g_coarse_dev = NULL;
	}
	return false;
}

/*
 * Drain fine DATA/MAPPED memory from @ctx->pending_pa to the exclusive @end,
 * after invalidation. The caller holds the leaf lock and initializes the cursor.
 * DATA returns to DELEGATED through the cache-maintenance helper; DEV needs no
 * cache maintenance. Remaining DATA/MAPPED states prevent tracking transitions,
 * so each lookup must succeed.
 *
 * Return true on a pending IRQ with the cursor at the next undone granule,
 * or false when the block is complete. No backing-granule lock is retained.
 */
static bool rtt_unmap_drain_fine(struct sro_unmap_ctx *ctx,
			       unsigned long end,
			       enum rtt_unmap_flavor flavor)
{
	while (ctx->pending_pa < end) {
		unsigned long tracking_size;

		if (rtt_unmap_irq_pending()) {
			return true;
		}

		if (flavor == RTT_UNMAP_FLAVOR_DATA) {
			struct granule *g_data;
			unsigned long ret __unused;

			ret = tr_find_lock_active_granule(ctx->pending_pa,
					GRANULE_STATE_DATA, &g_data, &tracking_size);
			assert(ret == RMI_SUCCESS);
			assert(tracking_size == GRANULE_SIZE);
			granule_unlock_transition_to_delegated(g_data);
		} else {
			struct dev_granule *g_dev;
			__unused enum dev_coh_type type;
			unsigned long ret __unused;

			ret = tr_find_lock_active_dev_granule(ctx->pending_pa,
					DEV_GRANULE_STATE_MAPPED, &g_dev, &type,
					&tracking_size);
			assert(ret == RMI_SUCCESS);
			assert(tracking_size == GRANULE_SIZE);
			dev_granule_unlock_transition(g_dev, DEV_GRANULE_STATE_DELEGATED);
		}

		ctx->pending_pa += tracking_size;
	}

	return false;
}

/*
 * Walk queued address ranges and drain their backing memory after invalidation.
 * The leaf must be locked and @list sorted by ascending PA. Fine DATA/MAPPED
 * states or coarse PARTIAL ownership prevent tracking changes across yields.
 * UNPROT has no backing-memory drain and must not call this helper.
 *
 * Both tracking modes share the list/block cursors and initialize @pending_pa
 * on block entry. The selected drain helper resumes at that PA and either
 * yields with progress retained or completes the block. Return true on yield,
 * or false once every block is drained. The list remains intact for Host output.
 * Leaf references and S2TTE pending markers are retained until the caller's
 * non-yieldable clear-marks pass, keeping the RTT chain and RD alive.
 */
static bool rtt_unmap_drain_pending(struct sro_unmap_ctx *ctx,
				    struct addr_list *list,
				    enum rtt_unmap_flavor flavor)
{
	assert((flavor == RTT_UNMAP_FLAVOR_DATA) ||
	       (flavor == RTT_UNMAP_FLAVOR_DEV));

	while (ctx->pending_desc_idx < list->count) {
		unsigned long base, blk_size, cnt, st;
		unsigned long blk_base, blk_end;
		int level;
		bool ok, yielded;

		ok = addr_list_peek_desc(list, ctx->pending_desc_idx,
					 &base, &level, &cnt, &st);
		assert(ok);
		(void)ok;
		(void)st;
		blk_size = XLAT_BLOCK_SIZE(level);

		if (ctx->pending_blk_idx >= cnt) {
			/*
			 * Descriptor exhausted; advance to the next one.
			 */
			ctx->pending_blk_idx = 0UL;
			ctx->pending_desc_idx++;
			ctx->pending_pa = ~0UL;
			continue;
		}

		/* Within a descriptor PAs are uniform: base + idx*blk_size. */
		blk_base = base + (ctx->pending_blk_idx * blk_size);
		blk_end = blk_base + blk_size;

		/*
		 * On first entry to a block, initialize pending_pa to the
		 * block base. On resume after a yield it already points at
		 * the next undone granule within this block.
		 */
		if (ctx->pending_pa == ~0UL) {
			ctx->pending_pa = blk_base;
		}
		assert(ctx->pending_pa >= blk_base);
		assert(ctx->pending_pa < blk_end);

		if ((ctx->g_coarse != NULL) || (ctx->g_coarse_dev != NULL)) {
			/* The owned coarse unit is the sole queued block. */
			assert((list->count == 1U) && (cnt == 1UL));
			assert(blk_base == ctx->backing_addr);
			assert(blk_size == tracking_region_get_size());
			yielded = rtt_unmap_drain_coarse(ctx, blk_end);
		} else {
			yielded = rtt_unmap_drain_fine(ctx, blk_end, flavor);
		}
		if (yielded) {
			return true;
		}

		ctx->pending_pa = ~0UL;
		ctx->pending_blk_idx++;
	}

	return false;
}

/*
 * Poll the outstanding SMMU CMD_SYNC while there is no interrupt to service.
 * Return true when the caller must yield with its pending marker intact.
 */
static bool rtt_unmap_smmu_sync_yield(struct sro_unmap_ctx *ctx)
{
	assert(ctx->smmu_tlbi_pending);

	while (!smmuv3_cmd_sync_is_complete(&ctx->smmu_cmd_sync)) {
		if (rtt_unmap_irq_pending()) {
			return true;
		}
		smmuv3_cmd_sync_wait();
	}

	return false;
}

/*
 * Issue the deferred stage-2 TLB and (when DA is enabled) SMMU TLB/ATC
 * invalidation for a single IPA on behalf of the SRO @ctx. Return true when
 * an IRQ requires yielding before CMD_SYNC completion.
 */
static bool rtt_unmap_invalidate_pending(struct sro_unmap_ctx *ctx,
					 unsigned long addr, long level,
					 unsigned long s2tte_idx)
{
	int ret;

	/* Allow the SMMU to process its commands during the CPU invalidation. */
	if (ctx->da_enabled) {
		ret = smmuv3_inv_at_level_per_vmids_submit(ctx->vmid_list,
							      ctx->nvmids, addr, level,
							      1UL, true,
							      &ctx->smmu_cmd_sync);
		if (ret != 0) {
			ERROR("smmuv3_inv_at_level_per_vmids_submit(0x%lx %ld) error %d\n",
			      addr, level, ret);
			panic();
		}
	}

	s2tt_invalidate_page_block_per_vmids(ctx->enable_lpa2, ctx->vmid_list,
					     ctx->nvmids, addr, level);

	if (!ctx->da_enabled) {
		return false;
	}

	ctx->smmu_tlbi_idx = s2tte_idx;
	ctx->smmu_tlbi_pending = true;
	if (rtt_unmap_smmu_sync_yield(ctx)) {
		return true;
	}
	ctx->smmu_tlbi_pending = false;

	return false;
}

/*
 * Yieldable TLBI pass over a mapped leaf table, shared by
 * RMI_RTT_DATA_UNMAP, RMI_RTT_UNPROT_UNMAP and RMI_RTT_DEV_UNMAP.
 *
 * For each entry carrying our handle and the S2TTE_SW_TLBI_PENDING bit,
 * issue the stage-2 (and SMMU when DA is enabled) TLB invalidation that
 * the sweep deferred. With DA enabled, submit the SMMU commands and poll
 * their CMD_SYNC completion until it completes or an IRQ becomes pending.
 * Clear the TLBI-pending bit only after completion. The IPA is reconstructed
 * from the cached leaf base IPA and entry index at @ctx->leaf_level. The
 * drain-pending bit and SRO handle are left in place. A separate,
 * non-yieldable pass removes them once this pass has completed.
 *
 * On a resume after yielding for an IRQ while CMD_SYNC is outstanding, the
 * stored TTE index is checked first. Once it completes, the walk restarts
 * from entry 0 but only entries still carrying this SRO handle and
 * S2TTE_SW_TLBI_PENDING trigger invalidation.
 *
 * A pending physical IRQ is sampled before processing each entry; on
 * a pending IRQ the function returns true (yielded). Entries belonging
 * to other in-flight SROs are left untouched. Caller must hold the
 * leaf RTT lock and have @s2tt mapped.
 *
 * On completion, set @ctx->tlbi_done and return false. Later calls return
 * false without rescanning or sampling IRQs, allowing the drain to progress.
 */
static bool rtt_unmap_tlbi_pending(struct sro_unmap_ctx *ctx,
				   unsigned long *s2tt)
{
	unsigned long map_size;
	unsigned long i;

	if (ctx->tlbi_done) {
		return false;
	}

	map_size = s2tte_map_size((int)ctx->leaf_level);
	if (ctx->smmu_tlbi_pending) {
		unsigned long s2tte;

		if (rtt_unmap_smmu_sync_yield(ctx)) {
			return true;
		}

		s2tte = s2tte_read(&s2tt[ctx->smmu_tlbi_idx]);
		assert(s2tte_drain_pending(s2tte));
		assert(s2tte_drain_handle(s2tte) == ctx->sro_handle);
		assert(s2tte_tlbi_pending(s2tte));
		s2tte_write(&s2tt[ctx->smmu_tlbi_idx],
			    s2tte_clear_tlbi_pending(s2tte));
		ctx->smmu_tlbi_pending = false;
	}

	for (i = 0UL; i < S2TTES_PER_S2TT; i++) {
		unsigned long s2tte;

		if (rtt_unmap_irq_pending()) {
			return true;
		}

		s2tte = s2tte_read(&s2tt[i]);

		if (s2tte_drain_pending(s2tte) &&
		    (s2tte_drain_handle(s2tte) == ctx->sro_handle) &&
		    s2tte_tlbi_pending(s2tte)) {
			unsigned long addr = ctx->leaf_base_ipa +
					     (i * map_size);

			if (rtt_unmap_invalidate_pending(ctx, addr,
							 ctx->leaf_level, i)) {
				return true;
			}

			s2tte_write(&s2tt[i],
				    s2tte_clear_tlbi_pending(s2tte));
		}
	}

	ctx->tlbi_done = true;
	return false;
}

/*
 * Non-yieldable pass: clear the SW drain marker on every entry carrying
 * our SRO handle and drop one leaf-RTT refcount per cleared entry (for
 * DATA the long-lived data_create() pin, for DEV the long-lived
 * dev_map() pin, and for UNPROT the transient pin the sweep took).
 *
 * Caller must hold the leaf RTT lock and have @s2tt mapped, and must
 * have already run rtt_unmap_tlbi_pending() to completion so no entry
 * still owes a TLBI when its drain marker is cleared.
 */
static void rtt_unmap_clear_marks_and_drop(struct sro_unmap_ctx *ctx,
				  unsigned long *s2tt)
{
	unsigned long i;

	for (i = 0UL; i < S2TTES_PER_S2TT; i++) {
		unsigned long s2tte = s2tte_read(&s2tt[i]);

		if (!s2tte_drain_pending(s2tte) ||
		    (s2tte_drain_handle(s2tte) != ctx->sro_handle)) {
			continue;
		}
		assert(!s2tte_tlbi_pending(s2tte));

		s2tte_write(&s2tt[i],
			    s2tte_clear_drain_pending(s2tte));
		atomic_granule_put_release(ctx->g_llt);
	}
}

/*
 * Single deferred-work entry point invoked by the initial runner (per
 * leaf sweep) and the SRO_OP_CONTINUE callbacks.
 *
 * Runs the deferred phases in order on the SRO @ctx. TLBI is completed
 * before any granule the host might observe in a different state:
 *   1. rtt_unmap_tlbi_pending(): issue the stage-2 (and SMMU) TLB
 *      invalidations for entries the sweep stamped. Requires the leaf
 *      locked and @s2tt mapped. The SMMU completion is polled until it
 *      completes or an IRQ becomes pending. On an IRQ, the function yields
 *      with the TTE marker intact. Once complete, the entry's TLBI bit is
 *      cleared. The drain mark and handle remain until phase 3.
 *   2. (DATA_UNMAP and DEV_UNMAP only) rtt_unmap_drain_pending():
 *      transition every queued backing granule in @list back to
 *      DELEGATED in ascending PA order, with IRQ-yield between granules.
 *      Does not touch the leaf RTT.
 *   3. rtt_unmap_clear_marks_and_drop(): clear the SW drain marks left behind
 *      by the sweep, then drop one leaf-RTT refcount per cleared
 *      entry. Requires the leaf locked and @s2tt mapped.
 *
 * @flavor selects whether phase 2 drains DATA granules, DEV granules,
 * or is skipped for UNPROT. All flavors hold one leaf-RTT refcount per
 * stamped entry until phase 3, so mark clearing is identical.
 *
 * Return true if a phase yields for a pending IRQ, including during CMD_SYNC.
 * On resume the caller re-maps @s2tt under the leaf lock and invokes this helper.
 * The TLBI helper remembers completion so drain continuations skip its pass.
 * Coarse PARTIAL ownership survives every yield without a lock.
 */
static bool rtt_unmap_drain_and_clear(struct sro_unmap_ctx *ctx,
				      struct addr_list *list,
				      unsigned long *s2tt,
				      enum rtt_unmap_flavor flavor)
{
	if (rtt_unmap_tlbi_pending(ctx, s2tt)) {
		return true;
	}

	if (flavor != RTT_UNMAP_FLAVOR_UNPROT) {
		if (rtt_unmap_drain_pending(ctx, list, flavor)) {
			return true;
		}
	}

	rtt_unmap_clear_marks_and_drop(ctx, s2tt);
	return false;
}

/*
 * Result of one rtt_unmap_run() invocation.
 */
enum rtt_unmap_run_result {
	RTT_UNMAP_RUN_DONE,	/* terminal; res->x[] filled */
	RTT_UNMAP_RUN_YIELD	/* deferred work remains; resume needed */
};

/*
 * Format the terminal SUCCESS / no-progress result for an RMI_RTT_*UNMAP
 * sweep by consuming @out_list according to @oaddr_type:
 *
 *   - NONE: the address list is discarded.
 *   - SINGLE: at most one descriptor is present; encode (oaddr | cnt | sz)
 *     into res->x[2].
 *   - LIST: copy descriptors to the host NS output buffer at @oaddr.
 *
 * @out_top is the IPA just past the last successfully unmapped entry.
 * If @out_list is empty no progress was made.
 */
static void rtt_unmap_format_result(unsigned int oaddr_type,
				    unsigned long oaddr,
				    struct addr_list *out_list,
				    unsigned long out_top,
				    struct smc_result *res)
{
	res->x[0] = RMI_SUCCESS;
	res->x[1] = out_top;
	res->x[2] = 0UL;
	res->x[3] = 0UL;

	if (addr_list_is_empty(out_list)) {
		return;
	}

	if (oaddr_type == RMI_ADDR_TYPE_SINGLE) {
		unsigned long base, blk_size, cnt, st;
		int level;
		bool ok;

		ok = addr_list_peek_desc(out_list, 0U,
					 &base, &level, &cnt, &st);
		assert(ok);
		(void)ok;
		(void)st;
		blk_size = XLAT_BLOCK_SIZE(level);
		res->x[2] = base |
			INPLACE(RMI_ADDR_RDESC_4K_CNT, cnt) |
			INPLACE(RMI_ADDR_RDESC_4K_SZ,
				xlat_blk_sz_to_addr_list_sz(blk_size));
	} else if (oaddr_type == RMI_ADDR_TYPE_LIST) {
		unsigned int copied = 0U;

		/*
		 * Write the collected range descriptors to the host NS
		 * buffer. A failure here can only happen if the host raced
		 * PAS away after our upfront NS check; we cannot undo the
		 * unmap, so report zero copied.
		 */
		(void)addr_list_partial_copy_to_host(out_list, oaddr,
					out_list->max_count,
					&copied);
		res->x[3] = (unsigned long)copied;
	}
}

/*
 * Run one invocation of an RMI_RTT_DATA_UNMAP, RMI_RTT_UNPROT_UNMAP
 * or RMI_RTT_DEV_UNMAP operation starting at @ctx->cur_base; the
 * flavor is taken from the current SRO context's init_command. @rd
 * must be the RD mapped via SLOT_RD; @g_rd is the locked granule
 * backing that mapping. @ctx must have all input fields populated
 * (oaddr, oaddr_type). The freed-address accumulator @out_list is for
 * this leaf sweep; if deferred work yields, the SRO context retains it
 * for the continue handler. Its drain cursors (pending_*) live in @ctx.
 *
 * One invocation processes at most one leaf RTT. If the request spans
 * additional leaves the host must reissue the same RMI command with a
 * fresh @base after consuming this invocation's terminal result. This
 * keeps the runner's lock and yield-state machine flat: a single leaf is
 * walked, swept, drained and cleared, and on yield only that leaf's
 * state needs to survive across the SRO continue.
 *
 * Acquires and releases all stage-2 RTT locks internally. As soon as
 * the root RTT lock is held the RD mapping and lock are released: from
 * then on the runner uses only the stack copy of the primary S2 context.
 * The held RTT lock prevents the realm from being torn down underneath
 * it.
 * For DATA/DEV, the sweep claims each queued coarse unit as PARTIAL before
 * deferred work. Fine DATA/MAPPED states also prevent tracking transitions
 * without a retained reader. A later region ends the prefix.
 *
 * Returns RTT_UNMAP_RUN_YIELD when the deferred work yielded on a pending IRQ
 * while progress has been made (out_list non-empty). This includes an IRQ
 * observed while waiting for CMD_SYNC completion.
 * res->x[] is left for the caller to format as RMI_INCOMPLETE.
 *
 * Returns RTT_UNMAP_RUN_DONE in all other cases. res->x[] is populated
 * with the terminal RMI_SUCCESS or RMI_ERROR_* result and any LIST
 * output is copied to the host's NS buffer. The terminal cases are:
 *
 *   Error cases (res->x[0] is an RMI_ERROR_*):
 *   - RMI_ERROR_RTT(level): walk landed on a leaf table whose block
 *     size does not divide @cur_base (host fold/unfold required).
 *   - RMI_ERROR_RTT(level): walk landed on a live entry whose block
 *     size is larger than the requested remaining range.
 *   - RMI_ERROR_RTT(level): on the very first iteration of the
 *     sweep, a TABLE descriptor was found at a non-leaf level, or
 *     (DATA only) an assigned_dev entry was found (raised by the
 *     per-flavor sweep helper).
 *   - RMI_ERROR_RTT_AUX(0): (DATA only) on the very first iteration
 *     of the sweep, an auxiliary RTT still has a live mapping
 *     covering the entry.
 *
 *   Success cases (res->x[0] is RMI_SUCCESS); the sweep stops at the
 *   first of:
 *   - the requested range was fully covered (cur_base reached @top);
 *   - the current leaf table reached its end (host reissues with the
 *     new base to cover the rest);
 *   - the sweep helper stopped before an error condition encountered
 *     past the first iteration: a TABLE descriptor, a wrong-flavor live
 *     entry (DATA or DEV), a live auxiliary mapping (DATA), a break in
 *     PA contiguity (SINGLE), or the output addr_list rejecting the
 *     block (LIST_COUNT cap reached with no merge possible).
 */
static enum rtt_unmap_run_result
rtt_unmap_run(struct granule *g_rd, struct rd *rd,
	      struct sro_unmap_ctx *ctx, unsigned long top,
	      struct addr_list *out_list,
	      struct smc_result *res)
{
	struct rtt_unmap_coarse_lock coarse = { 0 };
	struct s2tt_walk wi;
	struct s2tt_context s2_ctx;
	unsigned long *s2tt;
	unsigned long map_size;
	long level;
	bool yielded;
	enum data_unmap_step step;
	enum rtt_unmap_run_result ret = RTT_UNMAP_RUN_DONE;
	struct sro_context *sro = my_sro_ctx();
	enum rtt_unmap_flavor flavor;

	assert(sro != NULL);
	assert((sro->init_command == SMC_RMI_RTT_DATA_UNMAP) ||
	       (sro->init_command == SMC_RMI_RTT_UNPROT_UNMAP) ||
	       (sro->init_command == SMC_RMI_RTT_DEV_UNMAP));
	flavor = rtt_unmap_flavor_from_fid(sro->init_command);

	s2_ctx = rd->s2_ctx[PRIMARY_S2_CTX_ID];

	/* This runner is called from the entry path only. */
	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);

	/*
	 * Root RTT now locked. The walk and deferred work use only the
	 * stack copy of the primary S2 context.
	 */
	buffer_unmap(rd);
	granule_unlock(g_rd);

	s2tt_walk_lock_unlock(&s2_ctx, ctx->cur_base, S2TT_PAGE_LEVEL, &wi);
	s2tt = buffer_granule_mecid_map(wi.g_llt, SLOT_RTT, s2_ctx.mecid);
	assert(s2tt != NULL);

	/* Track the locked leaf and initialize ownership before the only sweep. */
	ctx->g_llt = wi.g_llt;
	ctx->g_coarse = NULL;
	ctx->g_coarse_dev = NULL;
	ctx->tlbi_done = false;

	level = wi.last_level;
	map_size = s2tte_map_size((int)level);

	/*
	 * cur_base must be aligned to the block size at the level the
	 * walk lands at; the host must fold/unfold otherwise.
	 */
	if ((ctx->cur_base & (map_size - 1UL)) != 0UL) {
		res->x[0] = pack_return_code_level(RMI_ERROR_RTT,
					(unsigned char)level);
		res->x[1] = 0UL;
		res->x[2] = 0UL;
		res->x[3] = 0UL;
		goto out_unmap_ll;
	}

	/*
	 * Cache the leaf's base IPA and level. The drain-completion
	 * walk uses these to reconstruct the IPA of every TTE stamped
	 * with S2TTE_SW_TLBI_PENDING, including from the SRO continue
	 * path where the original walk state is gone. wi.index is the
	 * offset of cur_base inside the leaf, so the leaf starts
	 * map_size * wi.index below cur_base.
	 */
	ctx->leaf_level = level;
	ctx->leaf_base_ipa = ctx->cur_base - (wi.index * map_size);

	step = rtt_unmap_one_table(&s2_ctx, s2tt,
				   wi.index, ctx->cur_base,
				   top, level, map_size,
				   out_list,
				   ctx, flavor, res, &coarse);
	if (step == DATA_UNMAP_STEP_ERROR) {
		/* res->x[] populated by helper. */
		goto out_unmap_ll;
	}

	/*
	 * Run the deferred phases for everything appended by the
	 * sweep. A pending IRQ, including while waiting for CMD_SYNC completion,
	 * causes a yield with the SRO drain cursors holding our position and
	 * the per-entry leaf refcounts still pinning @ctx->g_llt.
	 */
	if (flavor != RTT_UNMAP_FLAVOR_UNPROT) {
		addr_list_sort_by_addr(out_list);
	}

	yielded = rtt_unmap_drain_and_clear(ctx, out_list, s2tt, flavor);

	if (yielded) {
		/*
		 * Yield: leave res->x[] untouched (caller formats
		 * RMI_INCOMPLETE). The per-entry leaf-RTT refcounts are
		 * still held, so they naturally pin the leaf (and
		 * transitively the RTT chain and RD) until the SRO_CONTINUE
		 * call finishes the deferred work.
		 */
		ret = RTT_UNMAP_RUN_YIELD;
		goto out_unmap_ll;
	}

	/* Deferred work completed. */
	ctx->g_llt = NULL;

	if (!addr_list_is_empty(out_list)) {
		rtt_unmap_format_result(ctx->oaddr_type, ctx->oaddr,
					out_list, ctx->cur_base, res);
	} else {
		/*
		 * No output descriptors were produced. The sweep has
		 * already advanced ctx->cur_base past any non-live run and
		 * stopped at the next blocking entry, leaf boundary, or top.
		 */
		rtt_unmap_format_result(ctx->oaddr_type, ctx->oaddr,
					out_list, ctx->cur_base, res);
	}

out_unmap_ll:
	rtt_unmap_coarse_unlock(&coarse);
	buffer_unmap(s2tt);
	granule_unlock(wi.g_llt);
	return ret;
}

/*
 * SRO continue callback for RMI_RTT_DATA_UNMAP, RMI_RTT_UNPROT_UNMAP and
 * RMI_RTT_DEV_UNMAP.
 * Invoked from rmi_op_dispatch() in response to a host RMI_OP_CONTINUE
 * on a sealed handle. The SRO bookkeeping (find/seal/release) is
 * performed by smc_op_continue(); this callback completes the pending
 * SMMU invalidation and cache-maintenance work queued by the original
 * entry call and reports the resulting terminal status. No further RTT
 * walk or s2tte sweep is performed here: any range left between
 * @ctx->cur_base and the original @top will be picked up by a fresh
 * RMI_RTT_*UNMAP call from the host.
 *
 * RD is not touched here: the leaf RTT granule pinned by the still-
 * held per-entry refcounts keeps the RTT chain (and RD) alive across
 * the yield.
 * Fine DATA/MAPPED states and coarse PARTIAL ownership pin the backing
 * representation. Resume the owned coarse unit or look up the next fine
 * granule. No granule lock is kept across a return to the Host.
 */
void rtt_unmap_continue_handler(unsigned long fid,
				struct smc_result *res)
{
	struct sro_context *sro = my_sro_ctx();
	struct sro_unmap_ctx *ctx;
	unsigned long *s2tt;
	enum rtt_unmap_flavor flavor;
	bool yielded;

	assert(sro != NULL);
	assert(fid == SMC_RMI_OP_CONTINUE);
	assert((sro->init_command == SMC_RMI_RTT_DATA_UNMAP) ||
	       (sro->init_command == SMC_RMI_RTT_UNPROT_UNMAP) ||
	       (sro->init_command == SMC_RMI_RTT_DEV_UNMAP));
	(void)fid;

	flavor = rtt_unmap_flavor_from_fid(sro->init_command);

	ctx = &sro->unmap_ctx;
	assert(ctx->g_llt != NULL);

	granule_lock(ctx->g_llt, GRANULE_STATE_RTT);
	s2tt = buffer_granule_mecid_map(ctx->g_llt, SLOT_RTT, ctx->mecid);
	assert(s2tt != NULL);
	yielded = rtt_unmap_drain_and_clear(ctx, &sro->addr_list, s2tt, flavor);
	buffer_unmap(s2tt);
	granule_unlock(ctx->g_llt);

	if (yielded) {
		/*
		 * Still pending; the leaf RTT is still pinned by the
		 * un-dropped per-entry refcounts. Caller (smc_op_continue)
		 * re-seals the SRO context based on res->x[0] ==
		 * RMI_INCOMPLETE.
		 */
		res->x[0] = pack_return_code_incomplete(
				RMI_OP_MEM_REQ_NONE, RMI_OP_CANNOT_CANCEL);
		res->x[1] = 0UL;
		return;
	}

	/*
	 * Format the result from @sro->addr_list according to the
	 * caller's @oaddr_type and clear the leaf pointer.
	 */
	rtt_unmap_format_result(ctx->oaddr_type, ctx->oaddr,
				&sro->addr_list, ctx->cur_base, res);

	ctx->g_llt = NULL;
}

/*
 * Unmap a contiguous range of conventional memory mappings from the target
 * Protected IPA range [base, top).
 *
 * The walk to base is performed with hand-in-hand locking (parent + leaf
 * retained). The level at which the unmap is performed is determined by
 * the walk and is the same for every entry processed in a single call:
 * if base falls under a block mapping at L1/L2 the operation runs at L1/L2,
 * otherwise it runs at the L3 page level. One SMC call sweeps at most the
 * leaf table containing @base and stops at top or the end of that leaf.
 * If the request spans further leaves, the host retries with the returned
 * out_top as the new base.
 * Each mapped block must fit in one physical tracking region. Stop before
 * another region. The sweep claims coarse DATA as PARTIAL through deferred work,
 * keeping ownership across yields. Continuation resumes its owned unit directly.
 *
 * On a pending physical IRQ, including while waiting for SMMU CMD_SYNC
 * completion, the sweep yields cooperatively. If progress was made
 * (count > 0) and work remains (cur_base < top), the operation seals an
 * SRO context and returns RMI_INCOMPLETE; the host must call
 * RMI_OP_CONTINUE with the returned handle to resume. Otherwise the call
 * returns RMI_SUCCESS with the current progress (host retries with the
 * returned out_top as new base).
 *
 * If base is not aligned to the block size at the level the walk lands at,
 * the command returns RMI_ERROR_RTT(level) so the host can fold/unfold the
 * relevant entry before retrying.
 *
 * Supports oaddr_type NONE, SINGLE, and LIST. Output on terminal success:
 *   x[0] = RMI_SUCCESS | RMI_ERROR_*
 *   x[1] = out_top (top IPA actually unmapped; equals base if no progress)
 *   x[2] = RmiAddrRangeDesc4KB encoding (oaddr_first | count | SZ from level)
 *          for SINGLE on success, zero otherwise
 *   x[3] = number of range descriptors written to the host's address list
 *          for LIST on success, zero otherwise
 *
 * Output on yield:
 *   x[0] = RMI_INCOMPLETE | RMI_OP_MEM_REQ_NONE | RMI_OP_CANNOT_CANCEL
 *   x[1] = SRO context handle (pass to RMI_OP_CONTINUE)
 */
void smc_rtt_data_unmap(unsigned long rd_addr,
			unsigned long base,
			unsigned long top,
			unsigned long flags,
			unsigned long oaddr,
			struct smc_result *res)
{
	struct granule *g_rd;
	struct rd *rd;
	struct sro_context *sro;
	struct sro_unmap_ctx *ctx;
	unsigned long oaddr_type;
	unsigned long list_count;
	unsigned long ret;
	enum rtt_unmap_run_result step;
	int smmuv3_ret __unused;

	res->x[0] = RMI_ERROR_INPUT;

	/*
	 * Reserve an SRO context up front so a possible yield can seal
	 * without an additional allocation. RMI_OP_MEM_REQ_NONE: this
	 * operation does not transfer memory. Not cancellable.
	 */
	ret = sro_ctx_reserve(SMC_RMI_RTT_DATA_UNMAP, 0UL, false, false,
			      SMC_RMI_OP_CONTINUE);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	sro = my_sro_ctx();
	ctx = &sro->unmap_ctx;
	ctx->backing_addr = ~0UL;
	ret = tr_find_lock_granule(rd_addr, GRANULE_SIZE, GRANULE_STATE_RD, &g_rd);
	if (ret != RMI_SUCCESS) {
		sro_ctx_release();
		res->x[0] = ret;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	ret = validate_unmap_inputs(base, top, flags, oaddr, rd, true,
				    &oaddr_type, &list_count);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		buffer_unmap(rd);
		granule_unlock(g_rd);
		sro_ctx_release();
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);
	ctx = &sro->unmap_ctx;
	smmuv3_ret = smmuv3_cmd_sync_init(&ctx->smmu_cmd_sync,
				  xlat_low_va_to_pa((uintptr_t)&ctx->smmu_cmd_sync));
	assert(smmuv3_ret == 0);

	ctx->g_llt = NULL;
	ctx->oaddr = oaddr;
	ctx->oaddr_type = (unsigned int)oaddr_type;
	ctx->cur_base = base;
	ctx->pending_desc_idx = 0U;
	ctx->pending_blk_idx = 0UL;
	ctx->pending_pa = ~0UL;
	ctx->sro_handle = sro_ctx_my_handle();
	ctx->mecid = rd->s2_ctx[PRIMARY_S2_CTX_ID].mecid;
	ctx->enable_lpa2 =
		s2tt_lpa2_enabled(&rd->s2_ctx[PRIMARY_S2_CTX_ID]);
	ctx->leaf_base_ipa = 0UL;
	ctx->leaf_level = S2TT_PAGE_LEVEL;
	ctx->smmu_tlbi_idx = 0UL;
	ctx->smmu_tlbi_pending = false;

	/*
	 * Cache the VMID set and DA flag the drain-completion pass
	 * needs to issue the deferred stage-2 / SMMU invalidation in
	 * SRO context. For indirect_s2ap realms every plane has its
	 * own VMID; in the direct (single-VMID) case we collapse onto
	 * a 1-entry list so the drain can always use the per-VMID form.
	 * Snapshotting here lets the SRO continue handler invalidate
	 * without needing the RD granule.
	 */
	struct s2tt_context *primary_ctx =
		&rd->s2_ctx[PRIMARY_S2_CTX_ID];

	if (primary_ctx->indirect_s2ap) {
		unsigned int nplanes = realm_num_planes(rd);

		assert(nplanes <= MAX_TOTAL_PLANES);
		for (unsigned int i = 0U; i < nplanes; i++) {
			ctx->vmid_list[i] =
				plane_to_s2_context(rd, i)->vmid;
		}
		ctx->nvmids = nplanes;
	} else {
		ctx->vmid_list[0] = primary_ctx->vmid;
		ctx->nvmids = 1U;
	}
	ctx->da_enabled = rd->da_enabled;

	/*
	 * The SRO addr_list is the sole accumulator of freed DATA ranges
	 * for the sweep, regardless of @oaddr_type. The drain helper
	 * iterates it for cache maintenance, and the terminal result
	 * formatter consumes (or discards) it depending on @oaddr_type.
	 *
	 * The @max_count passed to addr_list_init() reflects the maximum
	 * number of `range` descriptors a successful sweep can produce:
	 *   - LIST:   host-supplied LIST_COUNT.
	 *   - SINGLE: 1. The sweep breaks at the first PA discontinuity,
	 *             so every collected OA folds into a single descriptor.
	 *   - NONE:   ADDR_LIST_MAX_RANGES. PAs in the leaf may be
	 *             discontiguous and the sweep must not stop early on
	 *             the addr_list cap; the descriptors are consumed
	 *             only by the drain (host gets no OA back).
	 */
	unsigned int max_count;

	switch (oaddr_type) {
	case RMI_ADDR_TYPE_LIST:
		max_count = (unsigned int)list_count;
		break;
	case RMI_ADDR_TYPE_SINGLE:
		max_count = 1U;
		break;
	default:
		max_count = (unsigned int)ADDR_LIST_MAX_RANGES;
		break;
	}
	addr_list_init(&sro->addr_list, LIST_TYPE_OUTPUT, max_count);


	step = rtt_unmap_run(g_rd, rd, ctx, top, &sro->addr_list, res);

	if (step == RTT_UNMAP_RUN_YIELD) {
		/*
		 * The deferred leaf-RTT refcounts taken by the sweep keep
		 * the RTT chain (and therefore the RD) alive until the
		 * SRO_CONTINUE drain drops the last one; no extra pin
		 * needed here.
		 */
		res->x[0] = pack_return_code_incomplete(
				RMI_OP_MEM_REQ_NONE, RMI_OP_CANNOT_CANCEL);
		res->x[1] = (unsigned long)sro_ctx_seal();
		return;
	}

	sro_ctx_release();
}

/*
 * Unmap a contiguous range of unprotected (NS) mappings from the
 * target IPA range [base, top).
 *
 * Mirrors smc_rtt_data_unmap for the !addr_in_par half-space: walks
 * to base, sweeps one leaf's assigned_ns entries to unassigned_ns
 * marked for deferred stage-2 TLBI, then runs the yieldable
 * TLBI-and-clear pass. On a pending IRQ, including while waiting for CMD_SYNC
 * completion, an SRO context is sealed and RMI_INCOMPLETE is returned; the
 * host must call RMI_OP_CONTINUE with the returned handle to resume.
 *
 * Supports oaddr_type NONE, SINGLE, and LIST.
 */
void smc_rtt_unprot_unmap(unsigned long rd_addr,
			  unsigned long base,
			  unsigned long top,
			  unsigned long flags,
			  unsigned long oaddr,
			  struct smc_result *res)
{
	struct granule *g_rd;
	struct rd *rd;
	struct sro_context *sro;
	struct sro_unmap_ctx *ctx;
	unsigned long oaddr_type;
	unsigned long list_count;
	unsigned long ret;
	enum rtt_unmap_run_result step;
	unsigned int max_count;
	int smmuv3_ret __unused;

	res->x[0] = RMI_ERROR_INPUT;

	ret = sro_ctx_reserve(SMC_RMI_RTT_UNPROT_UNMAP, 0UL, false, false,
			      SMC_RMI_OP_CONTINUE);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	ret = tr_find_lock_granule(rd_addr, GRANULE_SIZE,
				   GRANULE_STATE_RD, &g_rd);
	if (ret != RMI_SUCCESS) {
		sro_ctx_release();
		res->x[0] = ret;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	ret = validate_unmap_inputs(base, top, flags, oaddr, rd, false,
				    &oaddr_type, &list_count);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		buffer_unmap(rd);
		granule_unlock(g_rd);
		sro_ctx_release();
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);
	ctx = &sro->unmap_ctx;
	smmuv3_ret = smmuv3_cmd_sync_init(&ctx->smmu_cmd_sync,
				  xlat_low_va_to_pa((uintptr_t)&ctx->smmu_cmd_sync));
	assert(smmuv3_ret == 0);

	ctx->g_llt = NULL;
	ctx->oaddr = oaddr;
	ctx->oaddr_type = (unsigned int)oaddr_type;
	ctx->cur_base = base;
	ctx->sro_handle = sro_ctx_my_handle();
	ctx->mecid = rd->s2_ctx[PRIMARY_S2_CTX_ID].mecid;
	ctx->enable_lpa2 =
		s2tt_lpa2_enabled(&rd->s2_ctx[PRIMARY_S2_CTX_ID]);
	ctx->leaf_base_ipa = 0UL;
	ctx->leaf_level = S2TT_PAGE_LEVEL;
	ctx->smmu_tlbi_idx = 0UL;
	ctx->smmu_tlbi_pending = false;

	/*
	 * Cache the VMID set and DA flag the deferred TLBI pass needs
	 * to invalidate the freed entries on RMI_OP_CONTINUE without
	 * re-acquiring the RD granule. Direct (single-VMID) realms
	 * collapse onto a 1-entry list so the per-VMID call serves
	 * both encodings.
	 */
	struct s2tt_context *primary_ctx =
		&rd->s2_ctx[PRIMARY_S2_CTX_ID];

	if (primary_ctx->indirect_s2ap) {
		unsigned int nplanes = realm_num_planes(rd);

		assert(nplanes <= MAX_TOTAL_PLANES);
		for (unsigned int i = 0U; i < nplanes; i++) {
			ctx->vmid_list[i] =
				plane_to_s2_context(rd, i)->vmid;
		}
		ctx->nvmids = nplanes;
	} else {
		ctx->vmid_list[0] = primary_ctx->vmid;
		ctx->nvmids = 1U;
	}
	ctx->da_enabled = rd->da_enabled;

	switch (oaddr_type) {
	case RMI_ADDR_TYPE_LIST:
		max_count = (unsigned int)list_count;
		break;
	case RMI_ADDR_TYPE_SINGLE:
		max_count = 1U;
		break;
	default:
		max_count = (unsigned int)ADDR_LIST_MAX_RANGES;
		break;
	}
	addr_list_init(&sro->addr_list, LIST_TYPE_OUTPUT, max_count);

	step = rtt_unmap_run(g_rd, rd, ctx, top, &sro->addr_list, res);

	if (step == RTT_UNMAP_RUN_YIELD) {
		res->x[0] = pack_return_code_incomplete(
				RMI_OP_MEM_REQ_NONE, RMI_OP_CANNOT_CANCEL);
		res->x[1] = (unsigned long)sro_ctx_seal();
		return;
	}

	sro_ctx_release();
}
/*
 * Unmap a contiguous range of device memory mappings from the target
 * Protected IPA range [base, top).
 *
 * Mirrors smc_rtt_data_unmap, sharing the same yieldable sweep /
 * drain / clear pipeline via rtt_unmap_run(); the DEV flavor is
 * selected from sro->init_command. The drain phase first invalidates
 * the stamped stage-2 / SMMU mappings entry-by-entry with cooperative
 * IRQ checks, then transitions every freed dev_granule from MAPPED to
 * DELEGATED, also yieldably. On a pending IRQ, including while waiting for
 * CMD_SYNC completion, an SRO context is sealed and RMI_INCOMPLETE is
 * returned; the host must call
 * RMI_OP_CONTINUE with the returned handle to resume.
 * As for DATA_UNMAP, each block must fit in one tracking region; stop before
 * another region. Claim coarse MAPPED memory as PARTIAL through deferred
 * work, keeping ownership across yields until invalidation and drain complete.
 *
 * Supports oaddr_type NONE, SINGLE and LIST.
 */
void smc_rtt_dev_unmap(unsigned long rd_addr,
		       unsigned long base,
		       unsigned long top,
		       unsigned long flags,
		       unsigned long oaddr,
		       struct smc_result *res)
{
	struct granule *g_rd;
	struct rd *rd;
	struct sro_context *sro;
	struct sro_unmap_ctx *ctx;
	unsigned long oaddr_type;
	unsigned long list_count;
	unsigned long ret;
	enum rtt_unmap_run_result step;
	unsigned int max_count;
	int smmuv3_ret __unused;

	res->x[0] = RMI_ERROR_INPUT;

	ret = sro_ctx_reserve(SMC_RMI_RTT_DEV_UNMAP, 0UL, false, false,
			      SMC_RMI_OP_CONTINUE);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	sro = my_sro_ctx();
	ctx = &sro->unmap_ctx;
	ctx->backing_addr = ~0UL;
	ret = tr_find_lock_granule(rd_addr, GRANULE_SIZE, GRANULE_STATE_RD, &g_rd);
	if (ret != RMI_SUCCESS) {
		sro_ctx_release();
		res->x[0] = ret;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	ret = validate_unmap_inputs(base, top, flags, oaddr, rd, true,
				    &oaddr_type, &list_count);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		buffer_unmap(rd);
		granule_unlock(g_rd);
		sro_ctx_release();
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);
	ctx = &sro->unmap_ctx;
	smmuv3_ret = smmuv3_cmd_sync_init(&ctx->smmu_cmd_sync,
				  xlat_low_va_to_pa((uintptr_t)&ctx->smmu_cmd_sync));
	assert(smmuv3_ret == 0);

	ctx->g_llt = NULL;
	ctx->oaddr = oaddr;
	ctx->oaddr_type = (unsigned int)oaddr_type;
	ctx->cur_base = base;
	ctx->pending_desc_idx = 0U;
	ctx->pending_blk_idx = 0UL;
	ctx->pending_pa = ~0UL;
	ctx->sro_handle = sro_ctx_my_handle();
	ctx->mecid = rd->s2_ctx[PRIMARY_S2_CTX_ID].mecid;
	ctx->enable_lpa2 =
		s2tt_lpa2_enabled(&rd->s2_ctx[PRIMARY_S2_CTX_ID]);
	ctx->leaf_base_ipa = 0UL;
	ctx->leaf_level = S2TT_PAGE_LEVEL;
	ctx->smmu_tlbi_idx = 0UL;
	ctx->smmu_tlbi_pending = false;

	struct s2tt_context *primary_ctx =
		&rd->s2_ctx[PRIMARY_S2_CTX_ID];

	if (primary_ctx->indirect_s2ap) {
		unsigned int nplanes = realm_num_planes(rd);

		assert(nplanes <= MAX_TOTAL_PLANES);
		for (unsigned int i = 0U; i < nplanes; i++) {
			ctx->vmid_list[i] =
				plane_to_s2_context(rd, i)->vmid;
		}
		ctx->nvmids = nplanes;
	} else {
		ctx->vmid_list[0] = primary_ctx->vmid;
		ctx->nvmids = 1U;
	}
	ctx->da_enabled = rd->da_enabled;

	switch (oaddr_type) {
	case RMI_ADDR_TYPE_LIST:
		max_count = (unsigned int)list_count;
		break;
	case RMI_ADDR_TYPE_SINGLE:
		max_count = 1U;
		break;
	default:
		max_count = (unsigned int)ADDR_LIST_MAX_RANGES;
		break;
	}
	addr_list_init(&sro->addr_list, LIST_TYPE_OUTPUT, max_count);

	step = rtt_unmap_run(g_rd, rd, ctx, top, &sro->addr_list, res);

	if (step == RTT_UNMAP_RUN_YIELD) {
		res->x[0] = pack_return_code_incomplete(
				RMI_OP_MEM_REQ_NONE, RMI_OP_CANNOT_CANCEL);
		res->x[1] = (unsigned long)sro_ctx_seal();
		return;
	}

	sro_ctx_release();
}

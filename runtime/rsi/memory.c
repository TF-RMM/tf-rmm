/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <atomics.h>
#include <buffer.h>
#include <granule.h>
#include <planes.h>
#include <realm.h>
#include <rec.h>
#include <ripas.h>
#include <rsi-handler.h>
#include <s2ap_ind.h>
#include <s2tt.h>
#include <smc-rsi.h>

void handle_rsi_ipa_state_set(struct rec *rec,
			      struct rmi_rec_exit *rec_exit,
			      struct rsi_result *res)
{
	struct rec_plane *plane = rec_plane_0(rec);
	unsigned long base = plane->regs[1];
	unsigned long top = plane->regs[2];
	enum ripas ripas_val = (enum ripas)plane->regs[3];
	enum ripas_change_destroyed change_destroyed =
			(enum ripas_change_destroyed)plane->regs[4];

	/* Only Plane 0 can isuue RSI calls */
	assert(rec_is_plane_0_active(rec));

	if ((ripas_val > RIPAS_RAM) ||
	    !GRANULE_ALIGNED(base)  || !GRANULE_ALIGNED(top) ||
	    (top <= base)	    || /* Size is zero, or range overflows */
	    !region_in_rec_par(rec, base, top)) {
		res->action = UPDATE_REC_RETURN_TO_REALM;
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	rec->set_ripas.base = base;
	rec->set_ripas.top = top;
	rec->set_ripas.addr = base;
	rec->set_ripas.ripas_val = ripas_val;
	rec->set_ripas.change_destroyed = change_destroyed;

	rec_exit->exit_reason = RMI_EXIT_RIPAS_CHANGE;
	rec_exit->ripas_base = base;
	rec_exit->ripas_top = top;
	rec_exit->ripas_value = (unsigned char)ripas_val;

	res->action = UPDATE_REC_EXIT_TO_HOST;
	res->smc_res.x[0] = RSI_SUCCESS;
	res->smc_res.x[1] = top;
}

void handle_rsi_ipa_state_get(struct rec *rec,
			      struct rsi_result *res)
{
	unsigned long start = rec_plane_0(rec)->regs[1];
	unsigned long end = rec_plane_0(rec)->regs[2];
	unsigned long top = start;
	enum s2_walk_status ws;
	enum ripas ripas_val = RIPAS_EMPTY;

	/* Only Plane 0 can isuue RSI calls */
	assert(rec_is_plane_0_active(rec));

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if (!GRANULE_ALIGNED(start) || !addr_in_rec_par(rec, start) ||
	    !GRANULE_ALIGNED(end) || !addr_in_rec_par(rec, end - 1UL) ||
	    (start >= end)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	ws = realm_ipa_get_ripas(rec, start, end, &top, &ripas_val);
	if (ws == WALK_SUCCESS) {
		res->smc_res.x[0] = RSI_SUCCESS;
		res->smc_res.x[1] = (top > end) ? end : top;
		res->smc_res.x[2] = (unsigned long)ripas_val;
	} else {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
	}
}

static bool plane_id_is_valid(struct rec *rec, unsigned long plane_id)
{
	return plane_id < rec_num_planes(rec);
}

static bool perm_is_immutable(struct rd *rd, unsigned long perm_index)
{
	return atomic_test_bit_acquire_64(&rd->overlay_index_lock,
					  (unsigned int)perm_index);
}

/*
 * Validate the current cookie and, if needed, generate a new one. Return 'true'
 * if the passed cookie is valid or 'false' otherwise.
 *
 * If the cookie is null and the realm is using one translation table tree per
 * plane, it generates a new cookie.
 *
 * Cookie format:
 *
 * [63, 62, ................. 13, 12, 11, 10, ....... 01, 00]
 * \                               /  \                    /
 *  \----- Next base address -----/    \-- Next Context --/
 */
static bool validate_cookie(struct rec *rec, unsigned long *cookie,
			    unsigned long base, bool rtt_tree_pp)
{
	if (*cookie == 0UL) {
		if (rtt_tree_pp) {
			*cookie = RTT_COOKIE_CREATE(base, PRIMARY_S2_CTX_ID);
		}
		return true;
	}

	if (!rtt_tree_pp || (GET_RTT_BASE_FROM_COOKIE(*cookie) != base) ||
	    (GET_RTT_IDX_FROM_COOKIE(*cookie) > rec_num_planes(rec))) {
		return false;
	}

	return true;
}

void handle_rsi_mem_get_perm_value(struct rec *rec, struct rsi_result *res)
{
	struct rec_plane *plane = rec_plane_0(rec);
	unsigned long plane_id = plane->regs[1U];
	unsigned long perm_index = plane->regs[2U];
	unsigned long overlay_perm;
	struct rd *rd;
	struct s2tt_context *s2_ctx;

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if (!plane_id_is_valid(rec, plane_id)) {
		res->smc_res.x[0U] = RSI_ERROR_INPUT;
		return;
	}

	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	s2_ctx = plane_to_s2_context(rd, (unsigned int)plane_id);

	if (!s2ap_is_ovrl_perm_index_valid((unsigned int)perm_index)) {
		buffer_unmap(rd);
		res->smc_res.x[0U] = RSI_ERROR_INPUT;
		return;
	}

	overlay_perm = s2tt_ctx_get_overlay_perm_unlocked(s2_ctx);
	buffer_unmap(rd);

	res->smc_res.x[1U] = S2AP_IND_GET_PERM_VALUE(overlay_perm, perm_index);
	res->smc_res.x[0U] = RSI_SUCCESS;
}

void handle_rsi_mem_set_perm_value(struct rec *rec, struct rsi_result *res)
{
	struct rec_plane *plane = rec_plane_0(rec);
	unsigned long plane_id = plane->regs[1U];
	unsigned long perm_index = plane->regs[2U];
	unsigned long perm_value = plane->regs[3U];
	unsigned long overlay_perm;
	struct rd *rd;
	struct s2tt_context *s2_ctx;

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if (!(plane_id_is_valid(rec, plane_id) &&
	     s2ap_is_ovrl_perm_index_valid((unsigned int)perm_index) &&
	     (plane_id != PLANE_0_ID))) {
		res->smc_res.x[0U] = RSI_ERROR_INPUT;
		return;
	}

	granule_lock(rec->realm_info.g_rd, GRANULE_STATE_RD);
	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	if (perm_is_immutable(rd, perm_index)) {
		res->smc_res.x[0U] = RSI_ERROR_INPUT;
		goto out;
	}

	s2_ctx = plane_to_s2_context(rd, (unsigned int)plane_id);
	overlay_perm = s2tt_ctx_get_overlay_perm_locked(s2_ctx);
	overlay_perm = s2ap_set_overlay_perm(overlay_perm,
						 (unsigned int)perm_index,
						 perm_value);
	s2tt_ctx_set_overlay_perm(s2_ctx, overlay_perm);
	res->smc_res.x[0U] = RSI_SUCCESS;

out:
	buffer_unmap(rd);
	granule_unlock(rec->realm_info.g_rd);
}

void handle_rsi_mem_set_perm_index(struct rec *rec,
				   struct rmi_rec_exit *rec_exit,
				   struct rsi_result *res)
{
	struct rec_plane *plane = rec_plane_0(rec);
	unsigned long base = plane->regs[1U];
	unsigned long top = plane->regs[2U];
	unsigned long perm_index = plane->regs[3U];
	unsigned long cookie = plane->regs[4U];
	bool rtt_tree_pp;

	rtt_tree_pp = rec->realm_info.rtt_tree_pp;

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if (!(GRANULE_ALIGNED(base) && GRANULE_ALIGNED(top) && (base < top))) {
		res->smc_res.x[0U] = RSI_ERROR_INPUT;
		return;
	}

	if (!(region_in_rec_par(rec, base, top) &&
	      s2ap_is_ovrl_perm_index_valid((unsigned int)perm_index) &&
	      validate_cookie(rec, &cookie, base, rtt_tree_pp))) {
		res->smc_res.x[0U] = RSI_ERROR_INPUT;
		return;
	}

	res->action = UPDATE_REC_EXIT_TO_HOST;
	res->smc_res.x[0U] = RSI_SUCCESS;

	rec->set_s2ap.base = base;
	rec->set_s2ap.top = top;
	rec->set_s2ap.index = perm_index;
	rec->set_s2ap.cookie = cookie;

	rec_exit->exit_reason = RMI_EXIT_S2AP_CHANGE;
	rec_exit->s2ap_base = base;
	rec_exit->s2ap_top = top;
}

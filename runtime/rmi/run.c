/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <atomics.h>
#include <buffer.h>
#include <debug.h>
#include <esr.h>
#include <exit.h>
#include <gic.h>
#include <granule.h>
#include <inject_exp.h>
#include <psci.h>
#include <realm.h>
#include <rec.h>
#include <rsi-host-call.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc-rsi.h>
#include <smc.h>
#include <string.h>

static void reset_last_run_info(struct rec_plane *plane)
{
	plane->last_run_info.esr = 0UL;
}

static bool complete_mmio_emulation(struct rec *rec, struct rmi_rec_enter *rec_enter)
{
	struct rec_plane *plane = rec_active_plane(rec);
	unsigned long esr = plane->last_run_info.esr;
	unsigned int rt = esr_srt(esr);

	if ((rec_enter->flags & REC_ENTRY_FLAG_EMUL_MMIO) == 0UL) {
		return true;
	}

	/*
	 * If INJECT_SEA is set, we will only reach here if the condition
	 * for that flag is satisfied and has an effect on the Realm viz to
	 * Inject Data Abort at Unprotected IPA. Hence we skip EMUL_MMIO
	 * if the INJECT_SEA flag is set.
	 */
	if ((rec_enter->flags & REC_ENTRY_FLAG_INJECT_SEA) != 0UL) {
		return true;
	}

	/*
	 * The ISV bit is cleared as part of REC exit if the original data
	 * abort was not meant to be emulatable, i.e the address is either
	 * in PAR or is an AArch32 abort.
	 */
	if (((esr & MASK(ESR_EL2_EC)) != ESR_EL2_EC_DATA_ABORT) ||
	    ((esr & ESR_EL2_ABORT_ISV_BIT) == 0UL)) {
		/*
		 * MMIO emulation is requested but the REC did not exit with
		 * an emulatable exit.
		 */
		return false;
	}

	/*
	 * Emulate mmio read (unless the load is to xzr)
	 */
	if (!esr_is_write(esr) && (rt != 31U)) {
		unsigned long val;

		val = rec_enter->gprs[0] & access_mask(esr);

		if (esr_sign_extend(esr)) {
			unsigned int bit_count = access_len(esr) * 8U;
			unsigned long mask = (UL(1)) << U(bit_count - 1U);

			val = (val ^ mask) - mask;
			if (!esr_sixty_four(esr)) {
				val &= (1UL << 32U) - 1UL;
			}
		}

		plane->regs[rt] = val;
	}

	plane->pc = plane->pc + 4UL;
	return true;
}

static void complete_set_ripas(struct rec *rec)
{
	struct rec_plane *plane = rec_plane_0(rec);
	enum ripas ripas_val = rec->set_ripas.ripas_val;

	if (rec->set_ripas.base == rec->set_ripas.top) {
		return;
	}

	/* RIPAS change request can only come from the Plane 0. */
	assert(rec_is_plane_0_active(rec));

	/* Pending request from Realm */
	plane->regs[0] = RSI_SUCCESS;
	plane->regs[1] = rec->set_ripas.addr;

	if ((ripas_val == RIPAS_RAM) && (rec->set_ripas.addr != rec->set_ripas.top)
		 && (rec->set_ripas.response == REJECT)) {
		plane->regs[2] = RSI_REJECT;
	} else {
		plane->regs[2] = RSI_ACCEPT;
	}

	rec->set_ripas.base = 0UL;
	rec->set_ripas.top = 0UL;
}

static void complete_set_s2ap(struct rec *rec)
{
	struct rec_plane *plane = rec_plane_0(rec);
	bool rtt_tree_pp;
	unsigned long new_base;
	unsigned long cookie = 0UL;

	if ((rec->set_s2ap.base == 0UL) && (rec->set_s2ap.top == 0UL)) {
		/* No S2AP index change pending. Just return */
		return;
	}

	/* S2AP change request can only come from Plane 0. */
	assert(rec_is_plane_0_active(rec));

	rtt_tree_pp = rec->realm_info.rtt_tree_pp;

	if (rec->set_s2ap.response != REJECT) {
		struct rd *rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);

		assert(rd != NULL);

		set_perm_immutable(rd, rec->set_s2ap.index);

		buffer_unmap(rd);
	}

	new_base = rec->set_s2ap.base;
	if (rtt_tree_pp) {
		/*
		 * If we have updated the whole range of IPAs for the current
		 * tree, we need to verify if there are pending RTT trees to
		 * update and then create a new cookie to track the progress to
		 * the next tree starting at base IPA.
		 *
		 * If, on the other hand, we haven't updated the whole range of
		 * IPAs for the current tree, update the cookie with the new
		 * base and the current tree index.
		 *
		 * Note that the current cookie contains the base addr and the
		 * tree index from the last RSI_MEM_SET_PERM_INDEX call.
		 */
		unsigned long next_s2tt_idx;

		cookie = rec->set_s2ap.cookie;
		next_s2tt_idx = GET_RTT_IDX_FROM_COOKIE(cookie);
		assert(next_s2tt_idx < rec_num_planes(rec));

		if (new_base == rec->set_s2ap.top) {
			next_s2tt_idx++;

			if (next_s2tt_idx < rec_num_planes(rec)) {
				/*
				 * The current cookie should have the value
				 * of the original base, which will be used to
				 * create a new cookie to point to the base of
				 * the next RTT tree.
				 */
				new_base = GET_RTT_BASE_FROM_COOKIE(cookie);
				cookie = RTT_COOKIE_CREATE(new_base,
								  next_s2tt_idx);
			} else {
				/*
				 * Reset the cookie if we
				 * updated all the trees.
				 */
				cookie = 0UL;
			}
		} else {
			cookie = RTT_COOKIE_CREATE(new_base, next_s2tt_idx);
		}
	}

	rec->set_s2ap.base = 0UL;
	rec->set_s2ap.top = 0UL;
	rec->set_s2ap.index = 0UL;
	rec->set_s2ap.cookie = 0UL;

	plane->regs[0] = RSI_SUCCESS;
	plane->regs[1] = new_base;
	plane->regs[2] = (unsigned long)rec->set_s2ap.response;
	plane->regs[3] = cookie;
}

static bool complete_sea_insertion(struct rec *rec, struct rmi_rec_enter *rec_enter)
{
	struct rec_plane *plane = rec_active_plane(rec);
	unsigned long esr = plane->last_run_info.esr;
	unsigned long fipa;
	unsigned long hpfar = plane->last_run_info.hpfar;

	if ((rec_enter->flags & REC_ENTRY_FLAG_INJECT_SEA) == 0UL) {
		return true;
	}

	if ((esr & MASK(ESR_EL2_EC)) != ESR_EL2_EC_DATA_ABORT) {
		return false;
	}

	fipa = (hpfar & MASK(HPFAR_EL2_FIPA)) << HPFAR_EL2_FIPA_OFFSET;
	if (addr_in_rec_par(rec, fipa)) {
		return false;
	}

	inject_sync_idabort_rec(rec, ESR_EL2_ABORT_FSC_SEA);
	return true;
}


static void complete_sysreg_emulation(struct rec *rec, struct rmi_rec_enter *rec_enter)
{
	struct rec_plane *plane = rec_active_plane(rec);
	unsigned long esr = plane->last_run_info.esr;

	/* Rt bits [9:5] of ISS field cannot exceed 0b11111 */
	unsigned int rt = (unsigned int)ESR_EL2_SYSREG_ISS_RT(esr);

	if ((esr & MASK(ESR_EL2_EC)) != ESR_EL2_EC_SYSREG) {
		return;
	}

	if (ESR_EL2_SYSREG_IS_WRITE(esr)) {
		return;
	}

	/* Handle xzr */
	if (rt != 31U) {
		plane->regs[rt] = rec_enter->gprs[0];
	}
}

static bool complete_host_call(struct rec *rec, struct rmi_rec_run *rec_run)
{
	struct rsi_walk_result walk_result;

	if (!rec->host_call) {
		return true;
	}

	walk_result = complete_rsi_host_call(rec, &rec_run->enter);

	if (walk_result.abort) {
		/*
		 * The IPA where the result should be copied to (referred to by
		 * X1 at RSI_HOST_CALL) has RAM ripas but invalid mapping.
		 * Emulate the data abort against that IPA so that the host
		 * can bring the page in.
		 */
		unsigned long ipa = rec_active_plane(rec)->regs[1];

		emulate_stage2_data_abort(&rec_run->exit,
					  walk_result.rtt_level, ipa);
		return false;
	}

	rec->host_call = false;
	return true;
}

unsigned long smc_rec_enter(unsigned long rec_addr,
			    unsigned long rec_run_addr)
{
	struct granule *g_rec;
	struct granule *g_run;
	struct rec *rec;
	struct rec_plane *plane;
	struct rd *rd;
	struct rmi_rec_run rec_run;
	unsigned long realm_state, ret;
	bool success;
	int res;
	void *rec_aux;

	/*
	 * The content of `rec_run.exit` shall be returned to the host.
	 * Zero the structure to avoid the leakage of
	 * the content of the RMM's stack.
	 */
	(void)memset(&rec_run.exit, 0, sizeof(struct rmi_rec_exit));

	g_run = find_granule(rec_run_addr);
	if ((g_run == NULL) ||
		(granule_unlocked_state(g_run) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	/* For a REC to be runnable, it should be unused (refcount = 0) */
	res = find_lock_unused_granule(rec_addr, GRANULE_STATE_REC, &g_rec);
	if (res != 0) {
		switch (res) {
		case -EINVAL:
			return RMI_ERROR_INPUT;
		default:
			assert(res == -EBUSY);
			return RMI_ERROR_REC;
		}
	}

	/*
	 * Increment refcount. REC can have lock-free access, thus atomic access
	 * is required. Also, since the granule is only used for refcount
	 * update, only an atomic operation will suffice and release/acquire
	 * semantics are not required.
	 */
	atomic_granule_get(g_rec);

	/* Unlock the granule before switching to realm world. */
	granule_unlock(g_rec);

	success = ns_buffer_read(SLOT_NS, g_run, 0U,
				 sizeof(struct rmi_rec_enter), &rec_run.enter);

	if (!success) {
		/*
		 * Decrement refcount. Lock-free access to REC, thus atomic and
		 * release semantics is required.
		 */
		atomic_granule_put_release(g_rec);
		return RMI_ERROR_INPUT;
	}

	rec = buffer_granule_map(g_rec, SLOT_REC);
	assert(rec != NULL);

	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	realm_state = get_rd_state_unlocked(rd);
	buffer_unmap(rd);

	switch (realm_state) {
	case REALM_NEW:
		ret = pack_return_code(RMI_ERROR_REALM, 0U);
		goto out_unmap_buffers;
	case REALM_ACTIVE:
		break;
	case REALM_SYSTEM_OFF:
		ret = pack_return_code(RMI_ERROR_REALM, 1U);
		goto out_unmap_buffers;
	default:
		assert(false);
		break;
	}

	if (!rec->runnable) {
		ret = RMI_ERROR_REC;
		goto out_unmap_buffers;
	}

	/* REC with pending PSCI command is not schedulable */
	if (rec->psci_info.pending) {
		ret = RMI_ERROR_REC;
		goto out_unmap_buffers;
	}

	/* Map auxiliary granules */
	rec_aux = buffer_rec_aux_granules_map(rec->g_aux, rec->num_rec_aux);

	/*
	 * Check GIC state after checking other conditions but before doing
	 * anything which may have side effects.
	 */
	if (!gic_validate_state(rec_run.enter.gicv3_hcr,
				&rec_run.enter.gicv3_lrs[0])) {
		ret = RMI_ERROR_REC;
		goto out_unmap_aux_granules;
	}

	/*
	 * Note that the order of checking SEA insertion needs to be prior
	 * to checking mmio emulation as the conditions for the former flag
	 * having an effect (Data Abort at Unprotected IPA) are a superset
	 * of those for RMI_EMULATED_MMIO (Data Abort at Unprotected IPA and
	 * access was an emulatable read).
	 */
	if (!complete_sea_insertion(rec, &rec_run.enter)) {
		ret = RMI_ERROR_REC;
		goto out_unmap_aux_granules;
	}

	if (!complete_mmio_emulation(rec, &rec_run.enter)) {
		ret = RMI_ERROR_REC;
		goto out_unmap_aux_granules;
	}

	if (!complete_host_call(rec, &rec_run)) {
		ret = RMI_SUCCESS;
		goto out_unmap_aux_granules;
	}

	/* If active plane is not P0 ... */
	if (!rec_is_plane_0_active(rec)) {
		bool report_err = false;

		assert(rec->plane[1].sysregs != NULL);

		/*
		 * ... and either REC_ENTRY_FLAG_FORCE_P0 or
		 * REC_ENTRY_FLAG_INJECT_SEA are set, then exit the plane
		 * with sync exception and go back to P0. Else...
		 */
		if (((rec_run.enter.flags &
			(REC_ENTRY_FLAG_FORCE_P0 | REC_ENTRY_FLAG_INJECT_SEA)) != 0UL)) {
			report_err = !handle_plane_n_exit(rec, &rec_run.exit,
						ARM_EXCEPTION_SYNC_LEL, false);
		/*
		 * ... if the active plane is not the current GIC owner and there
		 * is a pending interrupt, then exit the plane with IRQ exception
		 * and go back to P0.
		 *
		 * Note, in both cases, that we do not need to save PN context
		 * back to the REC, as it was already saved when RMM first
		 * received the interrupt and exited to NS.
		 */
		} else if ((rec->active_plane_id != rec->gic_owner) &&
			   (gic_is_interrupt_pending(&rec_run.enter.gicv3_lrs[0]) ||
			   gic_is_maint_interrupt_pending(&rec->plane[1].sysregs->gicstate))) {
			report_err = !handle_plane_n_exit(rec, &rec_run.exit,
						ARM_EXCEPTION_IRQ_LEL, false);
		}

		if (report_err) {
			ret = RMI_ERROR_INPUT;
			goto out_unmap_aux_granules;
		}
	}

	plane = rec_active_plane(rec);
	assert(plane->sysregs != NULL);

	if (rec->active_plane_id == rec->gic_owner) {
		gic_copy_state_from_entry(&plane->sysregs->gicstate,
				(unsigned long *)&rec_run.enter.gicv3_lrs,
				rec_run.enter.gicv3_hcr);
	}

	rec->set_ripas.response =
		((rec_run.enter.flags & REC_ENTRY_FLAG_RIPAS_RESPONSE) == 0UL) ?
			ACCEPT : REJECT;
	complete_set_ripas(rec);

	rec->set_s2ap.response =
		((rec_run.enter.flags & REC_ENTRY_FLAG_S2AP_RESPONSE) == 0UL) ?
			ACCEPT : REJECT;
	complete_set_s2ap(rec);

	complete_sysreg_emulation(rec, &rec_run.enter);

	reset_last_run_info(plane);

	plane->sysregs->hcr_el2 = rec->common_sysregs.hcr_el2;
	if ((rec_run.enter.flags & REC_ENTRY_FLAG_TRAP_WFI) != 0UL) {
		plane->sysregs->hcr_el2 |= HCR_TWI;
	}
	if ((rec_run.enter.flags & REC_ENTRY_FLAG_TRAP_WFE) != 0UL) {
		plane->sysregs->hcr_el2 |= HCR_TWE;
	}

	ret = RMI_SUCCESS;

	rec_run_loop(rec, &rec_run.exit);

	/* Active plane might have changed during rec_run_loop() */
	plane = rec_active_plane(rec);
	assert(plane->sysregs != NULL);

	if (rec->active_plane_id == rec->gic_owner) {
		gic_copy_state_to_exit(&plane->sysregs->gicstate,
					   (unsigned long *)&rec_run.exit.gicv3_lrs,
					   &rec_run.exit.gicv3_hcr,
					   &rec_run.exit.gicv3_misr,
					   &rec_run.exit.gicv3_vmcr);
	}

out_unmap_aux_granules:
	/* Unmap auxiliary granules */
	buffer_rec_aux_unmap(rec_aux, rec->num_rec_aux);

out_unmap_buffers:
	buffer_unmap(rec);

	if (ret == RMI_SUCCESS) {
		if (!ns_buffer_write(
			SLOT_NS, g_run,
			(unsigned int)offsetof(struct rmi_rec_run, exit),
			sizeof(struct rmi_rec_exit), &rec_run.exit)) {
			ret = RMI_ERROR_INPUT;
		}
	}

	atomic_granule_put_release(g_rec);

	return ret;
}

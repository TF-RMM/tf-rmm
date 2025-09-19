/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_helpers.h>
#include <buffer.h>
#include <esr.h>
#include <exit.h>
#include <gic.h>
#include <granule.h>
#include <inject_exp.h>
#include <planes.h>
#include <psci.h>
#include <realm.h>
#include <rec.h>
#include <rsi-handler.h>
#include <rsi-logger.h>
#include <run.h>
#include <s2tt.h>
#include <simd.h>
#include <smc-rmi.h>
#include <smc-rsi.h>
#include <status.h>
#include <sysreg_traps.h>
#include <timers.h>

__dead2 static void system_abort(void)
{
	/*
	 * TODO: report the abort to the EL3.
	 * We need to establish the exact EL3 API first.
	 */
	panic();
}

static bool fixup_aarch32_data_abort(struct rec *rec, unsigned long *esr)
{
	unsigned long spsr = read_spsr_el2();
	(void)rec;

	if ((spsr & SPSR_EL2_nRW_AARCH32) != 0UL) {
		/*
		 * mmio emulation of AArch32 reads/writes is not supported.
		 */
		*esr &= ~ESR_EL2_ABORT_ISV_BIT;
		return true;
	}
	return false;
}

static unsigned long get_dabt_write_value(struct rec *rec, unsigned long esr)
{
	unsigned int rt = esr_srt(esr);

	/* Handle xzr */
	if (rt == 31U) {
		return 0UL;
	}

	return rec_active_plane(rec)->regs[rt] & access_mask(esr);
}

/*
 * Returns 'true' if access from @rec to @addr is within the Protected IPA space.
 */
static bool access_in_rec_par(struct rec *rec, unsigned long addr)
{
	/*
	 * It is OK to check only the base address of the access because:
	 * - The Protected IPA space starts at address zero.
	 * - The IPA width is below 64 bits, therefore the access cannot
	 *   wrap around.
	 */
	return addr_in_rec_par(rec, addr);
}

/*
 * Returns 'true' if the @ipa is in PAR and its RIPAS is 'empty'.
 *
 * @ipa must be aligned to the granule size.
 */
static bool ipa_is_empty(unsigned long ipa, struct rec *rec)
{
	struct s2_walk_result s2_walk;
	enum s2_walk_status walk_status;

	assert(GRANULE_ALIGNED(ipa));

	walk_status = realm_ipa_to_pa(rec, ipa, &s2_walk);

	if (walk_status == WALK_SUCCESS) {
		granule_unlock(s2_walk.llt);
	}

	if ((walk_status != WALK_INVALID_PARAMS) &&
	    (s2_walk.ripas_val == RIPAS_EMPTY)) {
		return true;
	}
	return false;
}

static bool fsc_is_external_abort(unsigned long fsc)
{
	if (fsc == ESR_EL2_ABORT_FSC_SEA) {
		return true;
	}

	if ((fsc >= ESR_EL2_ABORT_FSC_SEA_TTW_START) &&
	    (fsc <= ESR_EL2_ABORT_FSC_SEA_TTW_END)) {
		return true;
	}

	return false;
}

static bool abort_is_permission_fault(unsigned long esr)
{
	unsigned long fsc = esr & MASK(ESR_EL2_ABORT_FSC);

	if ((fsc >= ESR_EL2_ABORT_FSC_PERM_FAULT_START) &&
	    (fsc <= ESR_EL2_ABORT_FSC_PERM_FAULT_END)) {
		return true;
	}

	return false;
}

/*
 * Handles Data/Instruction Aborts at a lower EL with External Abort fault
 * status code (D/IFSC).
 * Returns 'true' if the exception is the external abort and the `rec_exit`
 * structure is populated, 'false' otherwise.
 */
static bool handle_sync_external_abort(struct rec *rec,
				       struct rmi_rec_exit *rec_exit,
				       unsigned long esr)
{
	unsigned long fsc = esr & MASK(ESR_EL2_ABORT_FSC);
	unsigned long set = esr & MASK(ESR_EL2_ABORT_SET);
	(void)rec;

	if (!fsc_is_external_abort(fsc)) {
		return false;
	}

	switch (set) {
	case ESR_EL2_ABORT_SET_UER:
		/*
		 * The recoverable SEA.
		 * Inject the sync. abort into the Realm.
		 * Report the exception to the host.
		 */
		inject_sync_idabort(ESR_EL2_ABORT_FSC_SEA);
		/*
		 * Fall through.
		 */
	case ESR_EL2_ABORT_SET_UEO:
		/*
		 * The restartable SEA.
		 * Report the exception to the host.
		 * The REC restarts the same instruction.
		 */
		rec_exit->esr = esr & ESR_NONEMULATED_ABORT_MASK;

		/*
		 * The value of the HPFAR_EL2 is not provided to the host as
		 * it is undefined for external aborts.
		 *
		 * We also don't provide the content of FAR_EL2 because it
		 * has no practical value to the host without the HPFAR_EL2.
		 */
		break;
	case ESR_EL2_ABORT_SET_UC:
		/*
		 * The uncontainable SEA.
		 * Fatal to the system.
		 * Fall through.
		 */
	default:
		system_abort();
	}

	return true;
}

void emulate_stage2_data_abort(struct rmi_rec_exit *rec_exit,
			       unsigned long rtt_level,
			       unsigned long ipa)
{
	assert(rtt_level <= (unsigned long)S2TT_PAGE_LEVEL);

	/*
	 * Setup Exception Syndrome Register to emulate a real data abort
	 * and return to NS host to handle it.
	 */
	rec_exit->esr = (ESR_EL2_EC_DATA_ABORT |
			(ESR_EL2_ABORT_FSC_TRANSLATION_FAULT_L0 + rtt_level));
	rec_exit->far = 0UL;
	rec_exit->hpfar = ipa >> HPFAR_EL2_FIPA_OFFSET;
	rec_exit->exit_reason = RMI_EXIT_SYNC;
}

/*
 * Returns 'true' if the abort is handled and the RMM should return to the Realm,
 * and returns 'false' if the exception should be reported to the HS host.
 */
static bool handle_data_abort(struct rec *rec, struct rmi_rec_exit *rec_exit,
			      unsigned long esr)
{
	unsigned long far = 0UL;
	unsigned long hpfar = read_hpfar_el2();
	unsigned long fipa = (hpfar & MASK(HPFAR_EL2_FIPA)) << HPFAR_EL2_FIPA_OFFSET;
	unsigned long write_val = 0UL;
	bool empty_ipa;

	if (handle_sync_external_abort(rec, rec_exit, esr)) {
		/*
		 * All external aborts are immediately reported to the host.
		 */
		return false;
	}

	empty_ipa = ipa_is_empty(fipa, rec);
	if (rec_is_plane_0_active(rec)) {
		/*
		 * The SEA is injected back to Plane 0 if:
		 *	- The fetch was from 'empty' memory.
		 */
		if (empty_ipa) {
			inject_sync_idabort(ESR_EL2_ABORT_FSC_SEA);
			return true;
		}
	} else {
		/*
		 * Data aborts from Plane N to Plane 0 are
		 * reported when:
		 *	- There is a permission fault
		 *	- The fetch was from an 'empty' memory.
		 * Note that this may occur only if the abort is from PAR
		 */
		if (abort_is_permission_fault(esr) || empty_ipa) {
			assert(access_in_rec_par(rec, fipa));
			return handle_plane_n_exit(rec, rec_exit,
						   ARM_EXCEPTION_SYNC_LEL, true);
		}
	}

	if (fipa >= rec_ipa_size(rec)) {
		inject_sync_idabort(ESR_EL2_ABORT_FSC_SEA);
		return true;
	}

	/* The rest of data aborts are reported to the host */
	if (fixup_aarch32_data_abort(rec, &esr) ||
	    access_in_rec_par(rec, fipa)) {
		esr &= ESR_NONEMULATED_ABORT_MASK;
		goto end;
	}

	if (esr_is_write(esr)) {
		write_val = get_dabt_write_value(rec, esr);
	}

	far = read_far_el2() & ~GRANULE_MASK;
	esr &= ESR_EMULATED_ABORT_MASK;

end:
	rec_exit->esr = esr;
	rec_exit->far = far;
	rec_exit->hpfar = hpfar;
	rec_exit->gprs[0] = write_val;
	rec_exit->rtt_tree = (unsigned long)active_s2_context_idx(rec);

	return false;
}

/*
 * Returns 'true' if the abort is handled and the RMM should return to the Realm,
 * and returns 'false' if the exception should be reported to the NS host.
 */
static bool handle_instruction_abort(struct rec *rec, struct rmi_rec_exit *rec_exit,
				     unsigned long esr)
{
	unsigned long fsc = esr & MASK(ESR_EL2_ABORT_FSC);
	unsigned long fsc_type = fsc & ~MASK(ESR_EL2_ABORT_FSC_LEVEL);
	unsigned long hpfar = read_hpfar_el2();
	unsigned long fipa = (hpfar & MASK(HPFAR_EL2_FIPA)) << HPFAR_EL2_FIPA_OFFSET;
	bool empty_ipa, in_par;

	if (handle_sync_external_abort(rec, rec_exit, esr)) {
		/*
		 * All external aborts are immediately reported to the host.
		 */
		return false;
	}

	empty_ipa = ipa_is_empty(fipa, rec);
	in_par = access_in_rec_par(rec, fipa);
	if (rec_is_plane_0_active(rec)) {
		/*
		 * The SEA is injected back to Plane 0 if:
		 *	- The fetch was from 'empty' memory
		 *	- The fetch was from outside PAR
		 */
		if (empty_ipa || !in_par) {
			inject_sync_idabort(ESR_EL2_ABORT_FSC_SEA);
			return true;
		}
	} else {
		/*
		 * Instruction aborts from Plane N to Plane 0 are
		 * reported when:
		 *	- The fetch was from outside PAR
		 *	- There is a permission fault
		 *	- The fetch was from an 'empty' memory.
		 */
		if (abort_is_permission_fault(esr) || empty_ipa || !in_par) {
			return handle_plane_n_exit(rec, rec_exit,
						   ARM_EXCEPTION_SYNC_LEL, true);
		}
	}

	if (fsc_type != ESR_EL2_ABORT_FSC_TRANSLATION_FAULT) {
		unsigned long far = read_far_el2();

		/*
		 * TODO: Should this ever happen, or is it an indication of an
		 * internal consistency failure in the RMM which should lead
		 * to a panic instead?
		 */

		ERROR("Unhandled instruction abort:\n");
		ERROR("    FSC: %12s0x%02lx\n", " ", fsc);
		ERROR("    FAR: %16lx\n", far);
		ERROR("  HPFAR: %16lx\n", hpfar);
	}

	/* The rest of instruction aborts are reported to the host */
	rec_exit->hpfar = hpfar;
	rec_exit->esr = esr & ESR_NONEMULATED_ABORT_MASK;
	rec_exit->rtt_tree = (unsigned long)active_s2_context_idx(rec);

	return false;
}

/*
 * Handle FPU or SVE or SME exceptions.
 * Returns: true if the exception is handled.
 */
static bool handle_simd_exception(struct rec *rec, unsigned long esr)
{
	unsigned long esr_el2_ec = esr & MASK(ESR_EL2_EC);

	/*
	 * If the REC wants to use SVE and if SVE is not enabled for this REC
	 * then inject undefined abort. This can happen when CPU implements
	 * FEAT_SVE but the Realm didn't request this feature during creation.
	 */
	if ((esr_el2_ec == ESR_EL2_EC_SVE) && !rec->realm_info.simd_cfg.sve_en) {
		realm_inject_undef_abort();
		return true;
	}

	/*
	 * This is a special case where an SVE Realm accessing certain SVE or SME
	 * instructions will be reported as SME exception if RMM was REC entered
	 * with PSTATE.SM=1. RMM needs to distinguish between lazy save-restore
	 * for SVE and access to SME.
	 * Some cases:
	 * 1. If SVE is disabled for the realm, then RMM needs to inject UNDEF.
	 * 2. If SVE is enabled for the realm, RMM will restore SVE SIMD context
	 *    of the REC and will resume the Realm (this will get the CPU out of
	 *    streaming mode). While re-trying the faulting instruction if it
	 *    generates a SME exception, then RMM will inject undefined abort
	 *    since SME is not supported for Realm.
	 */
	if ((esr_el2_ec == ESR_EL2_EC_SME) &&
	    (!rec->realm_info.simd_cfg.sve_en ||
	     (rec->active_simd_ctx == rec->aux_data.simd_ctx))) {
		realm_inject_undef_abort();
		return true;
	}

	/*
	 * As REC uses lazy enablement, upon FPU/SVE/SME exception the active
	 * SIMD context must not be the REC's context
	 */
	assert(rec->active_simd_ctx != rec->aux_data.simd_ctx);

	/* Save the NS SIMD context and restore REC's SIMD context */
	rec->active_simd_ctx = simd_context_switch(rec->active_simd_ctx,
						   rec->aux_data.simd_ctx);

	/*
	 * As the REC SIMD context is now restored, enable SIMD flags in REC's
	 * cptr based on REC's SIMD configuration.
	 */
	SIMD_ENABLE_CPTR_FLAGS(&rec->realm_info.simd_cfg, rec_active_plane(rec)->sysregs->cptr_el2);

	/*
	 * Return 'true' indicating that this exception has been handled and
	 * execution can continue.
	 */
	return true;
}

void advance_pc(void)
{
	unsigned long pc = read_elr_el2();

	write_elr_el2(pc + 4UL);
}

static void reverse_pc(void)
{
	unsigned long pc = read_elr_el2();

	write_elr_el2(pc - 4UL);
}

static inline bool rsi_handler_needs_fpu(unsigned int id)
{
#ifdef RMM_FPU_USE_AT_REL2
	if ((id == SMC_RSI_ATTEST_TOKEN_CONTINUE) ||
	    (id == SMC_RSI_MEASUREMENT_EXTEND)) {
		return true;
	}
#else
	(void)id;
#endif
	return false;
}

/*
 * Return 'true' if execution should continue in the REC, otherwise return
 * 'false' to go back to the NS caller of REC.Enter.
 */
static bool handle_wfx_exception(struct rec *rec,
				 struct rmi_rec_exit *rec_exit,
				 unsigned long esr)
{
	bool ret;

	if (rec_is_plane_0_active(rec)) {
		/* WFx calls from Plane 0 are forwarded to the host */
		rec_exit->esr = (esr & MASK(ESR_EL2_EC)) | ESR_EL2_WFx_TI_BIT;
		advance_pc();
		return false;
	}

	/* WFx call from Plane N are forwarded to Plane 0 */
	advance_pc();
	ret = handle_plane_n_exit(rec, rec_exit, ARM_EXCEPTION_SYNC_LEL, true);

	if (!ret) {
		/*
		 * handle_plane_e_exit() returned false and therefore RMM needs
		 * to return to Host for Stage 2 fixup. Once the fixup is done,
		 * RMM must retry the same WFx instruction again, so we need to
		 * reverse Plane_N PC here before exiting to the Host.
		 */
		reverse_pc();
	}

	return ret;
}

/*
 * Return 'true' if execution should continue in the REC, otherwise return
 * 'false' to go back to the NS caller of REC.Enter.
 */
static bool handle_hvc_exception(struct rec *rec,
				 struct rmi_rec_exit *rec_exit)
{
	bool ret;

	if (rec_is_plane_0_active(rec)) {
		/* Plane 0 must use the SMC conduit for all services */
		realm_inject_undef_abort();
		return true;
	}

	/*
	 * Handle_plane_n_exit() expects the PC to point to the address of
	 * the instruction following the one that caused the exception. In
	 * the case of an HVC instruction, the PC is already advanced.
	 */
	ret = handle_plane_n_exit(rec, rec_exit, ARM_EXCEPTION_SYNC_LEL, true);

	if (!ret) {
		/*
		 * handle_plane_n_exit() returned false and therefore RMM needs
		 * to return to Host for Stage 2 fixup. Once the fixup is done,
		 * RMM must retry the same HVC instruction again, so we need to
		 * reverse Plane_N PC here before exiting to the Host.
		 */
		reverse_pc();
	}

	return ret;
}

/*
 * Return 'true' if no further process of the function pointed to by
 * @function_id is needed.
 */
static bool handle_rsi_from_pn(struct rec *rec, struct rmi_rec_exit *rec_exit,
			       struct rec_plane *plane,
			       unsigned int function_id, bool *p0_return)
{
	/*
	 * SMC calls from plane N cause plane exit to Plane 0 due to
	 * synchronous exception.
	 *
	 * The only exception to this rule is when SMC_RSI_HOST_CALL is
	 * invoked with plane->trap_hc == RSI_NO_TRAP, hence, filter this call.
	 */
	if (!(function_id == SMC_RSI_HOST_CALL) &&
			(plane->trap_hc != (bool)RSI_TRAP)) {
		advance_pc();
		*p0_return = handle_plane_n_exit(rec, rec_exit,
						 ARM_EXCEPTION_SYNC_LEL, true);

		/*
		 * If handle_plane_n_exit() returned false, RMM needs to return
		 * to Host for Stage 2 fixup. Once the fixup is doen, RMM must
		 * retry the same instruction again.
		 */
		if (!(*p0_return)) {
			reverse_pc();
		}

		return true;
	}

	return false;
}

/*
 * Return 'true' if execution should continue in the REC, otherwise return
 * 'false' to go back to the NS caller.
 */
static bool handle_realm_rsi(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	struct rsi_result res = {UPDATE_REC_RETURN_TO_REALM, 0UL,
				{{[0 ... SMC_RESULT_REGS-1] = 0UL}}};
	struct rec_plane *plane = rec_active_plane(rec);
	unsigned int function_id = (unsigned int)plane->regs[0];
	bool restore_simd_ctx = false;
	unsigned int i;
	bool rec_ret;
	bool p0_ret __unused;

	/*
	 * According to SMCCCv1.1+ if SMC call doesn't return result
	 * in register starting from X4, it must preserve its value.
	 */
	for (i = 4U; i < SMC_RESULT_REGS; ++i) {
		res.smc_res.x[i] = plane->regs[i];
	}

	/* Ignore SVE hint bit, until RMM supports SVE hint bit */
	function_id &= ~SMC_SVE_HINT;

	if (!rec_is_plane_0_active(rec)) {
		bool p0_return;

		if (handle_rsi_from_pn(rec, rec_exit, plane,
						function_id, &p0_return)) {
			return p0_return;
		}
	}

	assert(rec_is_plane_0_active(rec) || (function_id == SMC_RSI_HOST_CALL));

	RSI_LOG_SET(plane->regs);

	/* Ignore SVE hint bit, until RMM supports SVE hint bit */
	function_id &= ~SMC_SVE_HINT;

	if (rsi_handler_needs_fpu(function_id) == true) {
		simd_context_save(rec->active_simd_ctx);
		restore_simd_ctx = true;
	}

	switch (function_id) {
	case SMCCC_VERSION:
		res.action = UPDATE_REC_RETURN_TO_REALM;
		res.smc_res.x[0] = SMCCC_VERSION_NUMBER;
		break;
	case SMC32_PSCI_FID_MIN ... SMC32_PSCI_FID_MAX:
	case SMC64_PSCI_FID_MIN ... SMC64_PSCI_FID_MAX:
		handle_psci(rec, rec_exit, &res);
		break;
	case SMC_RSI_VERSION:
		handle_rsi_version(rec, &res);
		break;
	case SMC_RSI_FEATURES:
		handle_rsi_features(rec, &res);
		break;
	case SMC_RSI_ATTEST_TOKEN_INIT:
		handle_rsi_attest_token_init(rec, &res);
		break;
	case SMC_RSI_ATTEST_TOKEN_CONTINUE:
		handle_rsi_attest_token_continue(rec, rec_exit, &res);
		break;
	case SMC_RSI_MEASUREMENT_READ:
		handle_rsi_measurement_read(rec, &res);
		break;
	case SMC_RSI_MEASUREMENT_EXTEND:
		handle_rsi_measurement_extend(rec, &res);
		break;
	case SMC_RSI_REALM_CONFIG:
		handle_rsi_realm_config(rec, &res);
		break;
	case SMC_RSI_IPA_STATE_SET:
		handle_rsi_ipa_state_set(rec, rec_exit, &res);
		break;
	case SMC_RSI_IPA_STATE_GET:
		handle_rsi_ipa_state_get(rec, &res);
		break;
	case SMC_RSI_HOST_CALL:
		handle_rsi_host_call(rec, rec_exit, &res);
		break;
	case SMC_RSI_MEM_GET_PERM_VALUE:
		handle_rsi_mem_get_perm_value(rec, &res);
		break;
	case SMC_RSI_MEM_SET_PERM_INDEX:
		handle_rsi_mem_set_perm_index(rec, rec_exit, &res);
		break;
	case SMC_RSI_MEM_SET_PERM_VALUE:
		handle_rsi_mem_set_perm_value(rec, &res);
		break;
	case SMC_RSI_PLANE_ENTER:
		handle_rsi_plane_enter(rec, &res);
		break;
	case SMC_RSI_PLANE_REG_READ:
		handle_rsi_plane_reg_read(rec, &res);
		break;
	case SMC_RSI_PLANE_REG_WRITE:
		handle_rsi_plane_reg_write(rec, &res);
		break;
	default:
		res.action = UPDATE_REC_RETURN_TO_REALM;
		res.smc_res.x[0] = SMC_UNKNOWN;
		break;
	}

	if (restore_simd_ctx) {
		simd_context_restore(rec->active_simd_ctx);
	}

	/*
	 * If the plane didn't change, either emulate a stage 2 abort or
	 * advance PC. If handle_* opted to change planes, leave PC alone.
	 */
	if (((unsigned int)res.action & FLAG_PLANE_CHANGED) == 0U) {
		if (((unsigned int)res.action & FLAG_STAGE_2_ABORT) != 0U) {
			/*
			 * The RSI call cannot prograess because the IPA that
			 * was provided by the Realm has invalid mapping.
			 * Emulate the data abort against that IPA so that the
			 * host can bring the page in.
			 *
			 * All RSI calls except SMC_RSI_PLANE_ENTER hold the
			 * IPA in X1.
			 */
			unsigned int ipa_reg =
				(function_id == SMC_RSI_PLANE_ENTER) ? 2U : 1U;
			unsigned long ipa = plane->regs[ipa_reg];

			emulate_stage2_data_abort(rec_exit, res.rtt_level, ipa);
		} else {
			advance_pc();
		}
	}

	/* Update REC registers if requested */
	if (((unsigned int)res.action & FLAG_UPDATE_REC) != 0U) {
		for (i = 0U; i < SMC_RESULT_REGS; ++i) {
			plane->regs[i] = res.smc_res.x[i];
		}
	}

	rec_ret = (((unsigned int)res.action & FLAG_EXIT_TO_HOST) == 0U);
	p0_ret = (((unsigned int)res.action &
		   (FLAG_EXIT_TO_HOST | FLAG_PLANE_CHANGED)) == 0U);

	RSI_LOG_EXIT(function_id, plane->regs, p0_ret);

	return rec_ret;
}

/*
 * Return 'true' if the RMM handled the exception,
 * 'false' to return to the Non-secure host.
 */
static bool handle_exception_sync(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	const unsigned long esr = read_esr_el2();

	switch (esr & MASK(ESR_EL2_EC)) {
	case ESR_EL2_EC_WFX:
		return handle_wfx_exception(rec, rec_exit, esr);
	case ESR_EL2_EC_HVC:
		return handle_hvc_exception(rec, rec_exit);
	case ESR_EL2_EC_SMC:
		return handle_realm_rsi(rec, rec_exit);
	case ESR_EL2_EC_SYSREG: {
		bool ret = handle_sysreg_access_trap(rec, rec_exit, esr);
		return ret;
	}
	case ESR_EL2_EC_INST_ABORT:
		return handle_instruction_abort(rec, rec_exit, esr);
	case ESR_EL2_EC_DATA_ABORT:
		return handle_data_abort(rec, rec_exit, esr);
	case ESR_EL2_EC_FPU:
	case ESR_EL2_EC_SVE:
	case ESR_EL2_EC_SME:
		return handle_simd_exception(rec, esr);
	default:
		/*
		 * TODO: Check if there are other exit reasons we could
		 * encounter here and handle them appropriately
		 */
		break;
	}

	VERBOSE("Unhandled sync exit ESR: %08lx (EC: %lx ISS: %lx)\n",
		esr, EXTRACT(ESR_EL2_EC, esr), EXTRACT(ESR_EL2_ISS, esr));

	/*
	 * Zero values in esr, far & hpfar of 'rec_exit' structure
	 * will be returned to the NS host.
	 * The only information that may leak is when there was
	 * some unhandled/unknown reason for the exception.
	 */
	return false;
}

/*
 * Return 'true' if the RMM handled the exception, 'false' to return to the
 * Non-secure host.
 */
static bool handle_exception_serror_lel(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	const unsigned long esr = read_esr_el2();

	if ((esr & ESR_EL2_SERROR_IDS_BIT) != 0UL) {
		/*
		 * Implementation defined content of the esr.
		 */
		system_abort();
	}

	if ((esr & MASK(ESR_EL2_SERROR_DFSC)) != ESR_EL2_SERROR_DFSC_ASYNC) {
		/*
		 * Either Uncategorized or Reserved fault status code.
		 */
		system_abort();
	}

	switch (esr & MASK(ESR_EL2_SERROR_AET)) {
	case ESR_EL2_SERROR_AET_UEU:	/* Unrecoverable RAS Error */
	case ESR_EL2_SERROR_AET_UER:	/* Recoverable RAS Error */
		/*
		 * The abort is fatal to the current S/W. Inject the SError into
		 * the Realm so it can e.g. shut down gracefully or localize the
		 * problem at the specific EL0 application.
		 *
		 * Note: Consider shutting down the Realm here to avoid
		 * the host's attack on unstable Realms.
		 */
		inject_serror(rec, esr);
		/*
		 * Fall through.
		 */
	case ESR_EL2_SERROR_AET_CE:	/* Corrected RAS Error */
	case ESR_EL2_SERROR_AET_UEO:	/* Restartable RAS Error */
		/*
		 * Report the exception to the host.
		 */
		rec_exit->esr = esr & ESR_SERROR_MASK;
		break;
	case ESR_EL2_SERROR_AET_UC:	/* Uncontainable RAS Error */
		/*
		 * Fall through.
		 */
	default:
		/*
		 * Unrecognized Asynchronous Error Type
		 */
		system_abort();
	}

	return false;
}

static bool handle_exception_irq_lel(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	(void)rec;

	rec_exit->exit_reason = RMI_EXIT_IRQ;

	/*
	 * With GIC all virtual interrupt programming
	 * must go via the NS hypervisor.
	 */
	return false;
}

/* Returns 'true' when returning to Realm (S) and false when to NS */
bool handle_realm_exit(struct rec *rec, struct rmi_rec_exit *rec_exit, int exception)
{
	struct rec_plane *plane = rec_active_plane(rec);

	switch (exception) {
	case ARM_EXCEPTION_SYNC_LEL: {
		bool ret;

		/*
		 * TODO: Sanitize ESR to ensure it doesn't leak sensitive
		 * information.
		 */
		rec_exit->exit_reason = RMI_EXIT_SYNC;
		ret = handle_exception_sync(rec, rec_exit);
		if (!ret) {
			plane->last_run_info.esr = read_esr_el2();
			/*
			 * Clear the ISV bit in last_run_info so that on next REC entry
			 * RMM doesn't allow MMIO emulation for invalid cases.
			 */
			if ((rec_exit->esr & ESR_EL2_ABORT_ISV_BIT) == 0UL) {
				plane->last_run_info.esr &= ~ESR_EL2_ABORT_ISV_BIT;
			}
			plane->last_run_info.far = read_far_el2();
			plane->last_run_info.hpfar = read_hpfar_el2();
		}
		return ret;

		/*
		 * TODO: Much more detailed handling of exit reasons.
		 */
	}
	case ARM_EXCEPTION_IRQ_LEL:
		return handle_exception_irq_lel(rec, rec_exit);
	case ARM_EXCEPTION_FIQ_LEL:
		rec_exit->exit_reason = RMI_EXIT_FIQ;
		break;
	case ARM_EXCEPTION_SERROR_LEL: {
		const unsigned long esr = read_esr_el2();
		bool ret;

		/*
		 * TODO: Sanitize ESR to ensure it doesn't leak sensitive
		 * information.
		 */
		rec_exit->exit_reason = RMI_EXIT_SERROR;
		ret = handle_exception_serror_lel(rec, rec_exit);
		if (!ret) {
			plane->last_run_info.esr = esr;
			plane->last_run_info.far = read_far_el2();
			plane->last_run_info.hpfar = read_hpfar_el2();
		}
		return ret;
	}
	default:
		INFO("Unrecognized exit reason: %d\n", exception);
		break;
	}

	return false;
}

static void handle_plane_exit_syndrome(struct rsi_plane_exit *exit,
				       unsigned long exit_reason)
{
	const unsigned long esr_el2 = read_esr_el2();
	const unsigned long elr_el2 = read_elr_el2();
	const unsigned long far_el2 = read_far_el2();
	const unsigned long hpfar_el2 = read_hpfar_el2();

	exit->reason = exit_reason;
	exit->elr_el2 = elr_el2;
	exit->esr_el2 = esr_el2;
	exit->far_el2 = far_el2;
	exit->hpfar_el2 = hpfar_el2;
}

static void do_handle_plane_exit(int exception, struct rsi_plane_exit *exit)
{
	switch (exception) {
	case ARM_EXCEPTION_SYNC_LEL:
		handle_plane_exit_syndrome(exit, RSI_EXIT_SYNC);
		break;
	case ARM_EXCEPTION_IRQ_LEL:
		handle_plane_exit_syndrome(exit, RSI_EXIT_IRQ);
		break;
	default:
		ERROR("Unhandled Plane exit exception: 0x%x\n", exception);
		assert(false);
	}
}

static void copy_timer_state_to_plane_exit(STRUCT_TYPE sysreg_state * sysregs,
					   struct rsi_plane_exit *exit)
{
	exit->cntp_ctl = sysregs->pp_sysregs.cntp_ctl_el0;
	exit->cntp_cval = sysregs->pp_sysregs.cntp_cval_el0;
	exit->cntv_ctl = sysregs->pp_sysregs.cntv_ctl_el0;
	exit->cntv_cval = sysregs->pp_sysregs.cntv_cval_el0;
}

static void copy_state_to_plane_exit(struct rec_plane *plane,
				     struct rsi_plane_exit *exit)
{
	for (unsigned int i = 0; i < RSI_PLANE_NR_GPRS; i++) {
		exit->gprs[i] = plane->regs[i];
	}

	exit->pstate = plane->sysregs->pstate;
	copy_timer_state_to_plane_exit(plane->sysregs, exit);
	gic_copy_state_to_exit(&plane->sysregs->gicstate,
			(unsigned long *)&exit->gicv3_lrs,
			&exit->gicv3_hcr,
			&exit->gicv3_misr,
			&exit->gicv3_vmcr);
}

/*
 * Handles the exit from plane N
 *
 * If 'true' is returned:
 * - The Realm has switched to Plane 0. This include changes to the
 *   entire state of the platform, such as the timers or the GIC.
 * - The Realm can continue running
 *
 * If 'false' is returned:
 * - The Realm has remained on Plane N because the stage 2 mapping of
 *   `rsi_plane_run` page is not valid.
 * - The data abort against the `rsi_plane_run` page be emulated.
 * - The RMM should return to the host so that the host can fix the mapping.
 * - The caller must ensure that Plane N executes the same
 *   instruction the next time the Realm is scheduled.
 *
 * @save_restore_plane_state indicates whether the Plane N state needs to be
 * saved and Plane 0 needs to be restored. It is false when this function is
 * invoked from an RMI handler as the Plane N state would have already been
 * saved as part of previous exit and Plane 0 will be directly restored from
 * REC as part of REC_ENTER.
 * It is true, when invoked from an RSI handler.
 *
 * Note that this function expects the PC on Plane N to point to the instruction
 * after the one that caused the exception.
 */
bool handle_plane_n_exit(struct rec *rec,
			 struct rmi_rec_exit *rec_exit,
			 int exception,
			 bool save_restore_plane_state)
{
	enum s2_walk_status walk_status;
	struct s2_walk_result walk_res;
	struct rec_plane *plane_0, *plane_n;
	unsigned long run_ipa, ret;
	struct granule *gr;
	struct rsi_plane_run *run;

	assert(!rec_is_plane_0_active(rec));

	plane_0 = rec_plane_0(rec);
	plane_n = rec_active_plane(rec);

	/* RSI_PLANE_ENTER receives the run structure IPA on the second arg */
	run_ipa = plane_0->regs[2];

	/*
	 * Find the rsi_plane_run page where we should report the
	 * plane N exit to Plane 0.
	 */
	walk_status = realm_ipa_to_pa(rec, run_ipa, &walk_res);

	/*
	 * Alignment and Protected IPA checks were done by
	 * handle_rsi_plane_enter
	 */
	assert(walk_status != WALK_INVALID_PARAMS);

	if (walk_res.ripas_val == RIPAS_EMPTY) {
		/*
		 * Plane 0 has set the ripas of `rsi_plane_run` granule
		 * to "empty".
		 * Exit to Plane 0 with error. The content of
		 * Plane N will be lost.
		 */
		ret = RSI_ERROR_INPUT;
		goto out_return_to_plane_0;
	} else if (walk_status == WALK_FAIL) {
		/* `rsi_plane_run` page is either destroyed or unassigned_ram s2tte */
		emulate_stage2_data_abort(rec_exit, walk_res.rtt_level, run_ipa);

		return false;
	}

	assert(walk_status == WALK_SUCCESS);

	ret = RSI_SUCCESS;

	/* Save Plane N state to REC */
	if (save_restore_plane_state) {
		save_realm_state(plane_n);
	}

	/* Map rsi_plane_run granule to RMM address space */
	gr = find_granule(walk_res.pa);
	run = (struct rsi_plane_run *)buffer_granule_map(gr, SLOT_REALM);

	/* Zero the exit structure */
	(void)memset((void *)&run->exit, 0, sizeof(struct rsi_plane_exit));

	/* Copy target Plane state to exit structure */
	copy_state_to_plane_exit(plane_n, &run->exit);

	/* Populate other fields of exit structure */
	do_handle_plane_exit(exception, &run->exit);

	/* Unmap rsi_plane_run granule */
	buffer_unmap(run);

	/* Unlock last level RTT */
	granule_unlock(walk_res.llt);

out_return_to_plane_0:
	/* Return values to Plane 0 */
	plane_0->regs[0] = ret;
	plane_0->regs[1] = 0UL;
	plane_0->regs[2] = 0UL;
	plane_0->regs[3] = 0UL;

	/* Deactivate plane 0 */
	rec_deactivate_plane_n(rec);

	/* Return GIC ownership to Plane 0 if it was owned by the previous plane */
	if (rec->gic_owner != PLANE_0_ID) {
		/* We need to save/restore plane_n/plane_0 here */
		assert(save_restore_plane_state);

		gic_copy_state(&plane_0->sysregs->gicstate,
				&plane_n->sysregs->gicstate);

		rec->gic_owner = PLANE_0_ID;
	}

	/* Advance the PC on Plane 0 */
	plane_0->pc = plane_0->pc + 4UL;

	/* Restore Plane 0 state from REC */
	if (save_restore_plane_state) {
		restore_realm_state(rec, plane_0);
		/*
		 * Since we are returning to P0, we need to undo
		 * multiplex_el2_timer(), so we restore NS timer.
		 */
		hyp_timer_restore_state(&rec->ns->el2_timer);
	}

	return true;
}

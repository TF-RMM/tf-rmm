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
#include <psci.h>
#include <realm.h>
#include <rec.h>
#include <rsi-handler.h>
#include <rsi-logger.h>
#include <s2tt.h>
#include <simd.h>
#include <smc-rmi.h>
#include <smc-rsi.h>
#include <status.h>
#include <sysreg_traps.h>

static void system_abort(void)
{
	/*
	 * TODO: report the abort to the EL3.
	 * We need to establish the exact EL3 API first.
	 */
	assert(false);
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
	return rec->regs[rt] & access_mask(esr);
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
		 */
		system_abort();
		break;
	default:
		assert(false);
	}

	return true;
}

void emulate_stage2_data_abort(struct rec *rec,
			       struct rmi_rec_exit *rec_exit,
			       unsigned long rtt_level)
{
	unsigned long fipa = rec->regs[1];

	assert(rtt_level <= (unsigned long)S2TT_PAGE_LEVEL);

	/*
	 * Setup Exception Syndrom Register to emulate a real data abort
	 * and return to NS host to handle it.
	 */
	rec_exit->esr = (ESR_EL2_EC_DATA_ABORT |
			(ESR_EL2_ABORT_FSC_TRANSLATION_FAULT_L0 + rtt_level));
	rec_exit->far = 0UL;
	rec_exit->hpfar = fipa >> HPFAR_EL2_FIPA_OFFSET;
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

	if (handle_sync_external_abort(rec, rec_exit, esr)) {
		/*
		 * All external aborts are immediately reported to the host.
		 */
		return false;
	}

	/*
	 * The memory access that crosses a page boundary may cause two aborts
	 * with `hpfar_el2` values referring to two consecutive pages.
	 *
	 * Insert the SEA and return to the Realm if IPA is outside realm IPA space or
	 * the granule's RIPAS is EMPTY.
	 */
	if ((fipa >= rec_ipa_size(rec)) || ipa_is_empty(fipa, rec)) {
		inject_sync_idabort(ESR_EL2_ABORT_FSC_SEA);
		return true;
	}

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

	if (handle_sync_external_abort(rec, rec_exit, esr)) {
		/*
		 * All external aborts are immediately reported to the host.
		 */
		return false;
	}

	/*
	 * Insert the SEA and return to the Realm if:
	 * - IPA is outside realm IPA space
	 * - The instruction abort is at an Unprotected IPA, or
	 * - The granule's RIPAS is EMPTY
	 */
	if ((fipa >= rec_ipa_size(rec)) ||
			!access_in_rec_par(rec, fipa) || ipa_is_empty(fipa, rec)) {
		inject_sync_idabort(ESR_EL2_ABORT_FSC_SEA);
		return true;
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
		return false;
	}

	rec_exit->hpfar = hpfar;
	rec_exit->esr = esr & ESR_NONEMULATED_ABORT_MASK;

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
	SIMD_ENABLE_CPTR_FLAGS(&rec->realm_info.simd_cfg, rec->sysregs.cptr_el2);

	/*
	 * Return 'true' indicating that this exception has been handled and
	 * execution can continue.
	 */
	return true;
}

static void advance_pc(void)
{
	unsigned long pc = read_elr_el2();

	write_elr_el2(pc + 4UL);
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
static bool handle_realm_rsi(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	struct rsi_result res = { 0 };
	unsigned int function_id = (unsigned int)rec->regs[0];
	bool restore_simd_ctx = false;
	unsigned int i;

	RSI_LOG_SET(rec->regs);

	/*
	 * According to SMCCCv1.1+ if SMC call doesn't return result
	 * in register starting from X4, it must preserve its value.
	 */
	for (i = 4U; i < SMC_RESULT_REGS; ++i) {
		res.smc_res.x[i] = rec->regs[i];
	}

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
	default:
		res.action = UPDATE_REC_RETURN_TO_REALM;
		res.smc_res.x[0] = SMC_UNKNOWN;
		break;
	}

	if (restore_simd_ctx) {
		simd_context_restore(rec->active_simd_ctx);
	}

	if (((unsigned int)res.action & FLAG_UPDATE_REC) != 0U) {
		for (i = 0U; i < SMC_RESULT_REGS; ++i) {
			rec->regs[i] = res.smc_res.x[i];
		}
	}

	if (((unsigned int)res.action & FLAG_STAGE_2_ABORT) != 0U) {
		emulate_stage2_data_abort(rec, rec_exit, res.rtt_level);
	} else {
		advance_pc();
	}

	/* Log RSI call */
	RSI_LOG_EXIT(function_id, rec->regs);

	return (((unsigned int)res.action & FLAG_EXIT_TO_HOST) == 0U);
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
		rec_exit->esr = esr & (MASK(ESR_EL2_EC) | ESR_EL2_WFx_TI_BIT);
		advance_pc();
		return false;
	case ESR_EL2_EC_HVC:
		realm_inject_undef_abort();
		return true;
	case ESR_EL2_EC_SMC:
		return handle_realm_rsi(rec, rec_exit);
	case ESR_EL2_EC_SYSREG: {
		bool ret = handle_sysreg_access_trap(rec, rec_exit, esr);

		advance_pc();
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
		system_abort();
		break;
	default:
		/*
		 * Unrecognized Asynchronous Error Type
		 */
		assert(false);
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
			rec->last_run_info.esr = read_esr_el2();
			/*
			 * Clear the ISV bit in last_run_info so that on next REC entry
			 * RMM doesn't allow MMIO emulation for invalid cases.
			 */
			if ((rec_exit->esr & ESR_EL2_ABORT_ISV_BIT) == 0UL) {
				rec->last_run_info.esr &= ~ESR_EL2_ABORT_ISV_BIT;
			}
			rec->last_run_info.far = read_far_el2();
			rec->last_run_info.hpfar = read_hpfar_el2();
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
			rec->last_run_info.esr = esr;
			rec->last_run_info.far = read_far_el2();
			rec->last_run_info.hpfar = read_hpfar_el2();
		}
		return ret;
	}
	default:
		INFO("Unrecognized exit reason: %d\n", exception);
		break;
	}

	return false;
}

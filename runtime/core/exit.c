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
#include <memory_alloc.h>
#include <psci.h>
#include <realm.h>
#include <realm_attest.h>
#include <rec.h>
#include <rsi-config.h>
#include <rsi-handler.h>
#include <rsi-host-call.h>
#include <rsi-logger.h>
#include <rsi-memory.h>
#include <rsi-walk.h>
#include <run.h>
#include <simd.h>
#include <smc-rmi.h>
#include <smc-rsi.h>
#include <status.h>
#include <sysreg_traps.h>
#include <table.h>

void save_fpu_state(struct fpu_state *fpu);
void restore_fpu_state(struct fpu_state *fpu);

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

	assert(rtt_level <= RTT_PAGE_LEVEL);

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
	 * Insert the SEA and return to the Realm if the granule's RIPAS is EMPTY.
	 */
	if (ipa_is_empty(fipa, rec)) {
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
	 * - The instruction abort is at an Unprotected IPA, or
	 * - The granule's RIPAS is EMPTY
	 */
	if (!access_in_rec_par(rec, fipa) || ipa_is_empty(fipa, rec)) {
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
 * Handle FPU or SVE exceptions.
 * Returns: true if the exception is handled.
 */
static bool
handle_simd_exception(simd_t exp_type, struct rec *rec)
{
	/*
	 * If the REC wants to use SVE and if SVE is not enabled for this REC
	 * then inject undefined abort. This can happen when CPU implements
	 * FEAT_SVE but the Realm didn't request this feature during creation.
	 */
	if (exp_type == SIMD_SVE && rec_simd_type(rec) != SIMD_SVE) {
		realm_inject_undef_abort();
		return true;
	}

	/* FPU or SVE exception can happen only when REC hasn't used SIMD */
	assert(rec_is_simd_allowed(rec) == false);

	/*
	 * Allow the REC to use SIMD. Save NS SIMD state and restore REC SIMD
	 * state from memory to registers.
	 */
	simd_save_ns_state();
	rec_simd_enable_restore(rec);

	/*
	 * Return 'true' indicating that this exception has been handled and
	 * execution can continue.
	 */
	return true;
}

/*
 * Return 'false' if no IRQ is pending,
 * return 'true' if there is an IRQ pending, and need to return to host.
 */
static bool check_pending_irq(void)
{
	unsigned long pending_irq;

	pending_irq = read_isr_el1();

	return (pending_irq != 0UL);
}

static void advance_pc(void)
{
	unsigned long pc = read_elr_el2();

	write_elr_el2(pc + 4UL);
}

static void return_result_to_realm(struct rec *rec, struct smc_result result)
{
	rec->regs[0] = result.x[0];
	rec->regs[1] = result.x[1];
	rec->regs[2] = result.x[2];
	rec->regs[3] = result.x[3];
}

static inline bool rsi_handler_needs_fpu(unsigned int id)
{
#ifdef RMM_FPU_USE_AT_REL2
	if (id == SMC_RSI_ATTEST_TOKEN_CONTINUE ||
	    id == SMC_RSI_MEASUREMENT_EXTEND) {
		return true;
	}
#endif
	return false;
}

/*
 * Return 'true' if execution should continue in the REC, otherwise return
 * 'false' to go back to the NS caller of REC.Enter.
 */
static bool handle_realm_rsi(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	bool ret_to_rec = true;	/* Return to Realm */
	unsigned int function_id = (unsigned int)rec->regs[0];
	bool restore_rec_simd_state = false;

	RSI_LOG_SET(rec->regs);

	/* Ignore SVE hint bit, until RMM supports SVE hint bit */
	function_id &= ~MASK(SMC_SVE_HINT);

	if (rsi_handler_needs_fpu(function_id) == true) {
		/*
		 * RSI handler uses FPU at REL2, so actively save REC SIMD state
		 * if REC is using SIMD or NS SIMD state. Restore the same before
		 * return from this function.
		 */
		if (rec_is_simd_allowed(rec)) {
			rec_simd_save_disable(rec);
			restore_rec_simd_state = true;
		} else {
			simd_save_ns_state();
		}
	} else if (rec_is_simd_allowed(rec)) {
		/*
		 * If the REC is allowed to access SIMD, then we will enter RMM
		 * with SIMD traps disabled. So enable SIMD traps as RMM by
		 * default runs with SIMD traps enabled
		 */
		simd_disable();
	}

	switch (function_id) {
	case SMCCC_VERSION:
		rec->regs[0] = SMCCC_VERSION_NUMBER;
		break;
	case SMC_RSI_ABI_VERSION:
		rec->regs[0] = handle_rsi_version();
		break;
	case SMC32_PSCI_FID_MIN ... SMC32_PSCI_FID_MAX:
	case SMC64_PSCI_FID_MIN ... SMC64_PSCI_FID_MAX: {
		struct psci_result res;

		res = psci_rsi(rec,
			       function_id,
			       rec->regs[1],
			       rec->regs[2],
			       rec->regs[3]);

		if (!rec->psci_info.pending) {
			rec->regs[0] = res.smc_res.x[0];
			rec->regs[1] = res.smc_res.x[1];
			rec->regs[2] = res.smc_res.x[2];
			rec->regs[3] = res.smc_res.x[3];
		}

		if (res.hvc_forward.forward_psci_call) {
			unsigned int i;

			rec_exit->exit_reason = RMI_EXIT_PSCI;
			rec_exit->gprs[0] = function_id;
			rec_exit->gprs[1] = res.hvc_forward.x1;
			rec_exit->gprs[2] = res.hvc_forward.x2;
			rec_exit->gprs[3] = res.hvc_forward.x3;

			for (i = 4U; i < REC_EXIT_NR_GPRS; i++) {
				rec_exit->gprs[i] = 0UL;
			}

			advance_pc();
			ret_to_rec = false;
		}
		break;
	}
	case SMC_RSI_ATTEST_TOKEN_INIT:
		rec->regs[0] = handle_rsi_attest_token_init(rec);
		break;
	case SMC_RSI_ATTEST_TOKEN_CONTINUE: {
		struct attest_result res;
		while (true) {
			/*
			 * Possible outcomes:
			 *     if res.incomplete is true
			 *         if IRQ pending
			 *             check for pending IRQ and return to host
			 *         else try a new iteration
			 *     else
			 *         if RTT table walk has failed,
			 *             emulate data abort back to host
			 *         otherwise
			 *             return to realm because the token
			 *             creation is complete or input parameter
			 *             validation failed.
			 */
			handle_rsi_attest_token_continue(rec, &res);

			if (res.incomplete) {
				if (check_pending_irq()) {
					rec_exit->exit_reason = RMI_EXIT_IRQ;

					/* Copy the result to rec prior to return to host */
					return_result_to_realm(rec, res.smc_res);
					advance_pc();

					/* Return to NS host to handle IRQ. */
					ret_to_rec = false;
					break;
				}
			} else {
				if (res.walk_result.abort) {
					emulate_stage2_data_abort(
						rec, rec_exit,
						res.walk_result.rtt_level);
					ret_to_rec = false; /* Exit to Host */
					break;
				}

				/* Return to Realm */
				return_result_to_realm(rec, res.smc_res);
				break;
			}
		}
		break;
	}
	case SMC_RSI_MEASUREMENT_READ:
		rec->regs[0] = handle_rsi_read_measurement(rec);
		break;
	case SMC_RSI_MEASUREMENT_EXTEND:
		rec->regs[0] = handle_rsi_extend_measurement(rec);
		break;
	case SMC_RSI_REALM_CONFIG: {
		struct rsi_walk_smc_result res;

		res = handle_rsi_realm_config(rec);
		if (res.walk_result.abort) {
			emulate_stage2_data_abort(rec, rec_exit,
						  res.walk_result.rtt_level);
			ret_to_rec = false; /* Exit to Host */
		} else {
			/* Return to Realm */
			return_result_to_realm(rec, res.smc_res);
		}
		break;
	}
	case SMC_RSI_IPA_STATE_SET:
		if (handle_rsi_ipa_state_set(rec, rec_exit)) {
			rec->regs[0] = RSI_ERROR_INPUT;
		} else {
			advance_pc();
			ret_to_rec = false; /* Return to Host */
		}
		break;
	case SMC_RSI_IPA_STATE_GET: {
		struct rsi_walk_smc_result res;

		res = handle_rsi_ipa_state_get(rec);
		if (res.walk_result.abort) {
			emulate_stage2_data_abort(rec, rec_exit,
						  res.walk_result.rtt_level);
			/* Exit to Host */
			ret_to_rec = false;
		} else {
			/* Exit to Realm */
			return_result_to_realm(rec, res.smc_res);
		}
		break;
	}
	case SMC_RSI_HOST_CALL: {
		struct rsi_host_call_result res;

		res = handle_rsi_host_call(rec, rec_exit);

		if (res.walk_result.abort) {
			emulate_stage2_data_abort(rec, rec_exit,
						  res.walk_result.rtt_level);
			/* Exit to Host */
			ret_to_rec = false;
		} else {
			rec->regs[0] = res.smc_result;

			/*
			 * Return to Realm in case of error,
			 * parent function calls advance_pc()
			 */
			if (rec->regs[0] == RSI_SUCCESS) {
				advance_pc();

				/* Exit to Host */
				rec->host_call = true;
				rec_exit->exit_reason = RMI_EXIT_HOST_CALL;
				ret_to_rec = false;
			}
		}
		break;
	}
	default:
		rec->regs[0] = SMC_UNKNOWN;
		break;
	}

	if (rsi_handler_needs_fpu(function_id) == true) {
		if (restore_rec_simd_state == true) {
			rec_simd_enable_restore(rec);
		} else {
			simd_restore_ns_state();
		}
	} else if (rec_is_simd_allowed(rec)) {
		simd_enable(rec_simd_type(rec));
	}

	/* Log RSI call */
	RSI_LOG_EXIT(function_id, rec->regs, ret_to_rec);
	return ret_to_rec;
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
		if (!handle_realm_rsi(rec, rec_exit)) {
			return false;
		}
		/*
		 * Advance PC.
		 * HCR_EL2.TSC traps execution of the SMC instruction.
		 * It is not a routing control for the SMC exception.
		 * Trap exceptions and SMC exceptions have different
		 * preferred return addresses.
		 */
		advance_pc();
		return true;
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
		return handle_simd_exception(SIMD_FPU, rec);
	case ESR_EL2_EC_SVE:
		return handle_simd_exception(SIMD_SVE, rec);
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

	if (esr & ESR_EL2_SERROR_IDS_BIT) {
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
	};

	return false;
}

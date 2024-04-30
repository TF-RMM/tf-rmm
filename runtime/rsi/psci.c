/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <granule.h>
#include <psci.h>
#include <realm.h>
#include <rec.h>
#include <rsi-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <stdint.h>

/*
 * Copy @count GPRs from @rec to @rec_exit.
 * The remaining @rec_exit.gprs[] values are zero filled.
 */
static void forward_args_to_host(unsigned int count, struct rec *rec,
				 struct rmi_rec_exit *rec_exit)
{
	unsigned int i;

	assert(count <= 4U);

	for (i = 0U; i < count; ++i) {
		rec_exit->gprs[i] = rec->regs[i];
	}

	for (i = count; i < REC_EXIT_NR_GPRS; ++i) {
		rec_exit->gprs[i] = 0UL;
	}
}

static void psci_version(struct rsi_result *res)
{
	const unsigned long version_1_1 = (1UL << 16) | 1UL;

	res->action = UPDATE_REC_RETURN_TO_REALM;
	res->smc_res.x[0] = version_1_1;
}

static void psci_cpu_suspend(struct rec *rec, struct rmi_rec_exit *rec_exit,
			     struct rsi_result *res)
{
	res->action = UPDATE_REC_EXIT_TO_HOST;

	/*
	 * We treat all target power states as suspend requests,
	 * so all we need to do is forward the FID to the NS hypervisor,
	 * and we can ignore all the parameters.
	 */
	forward_args_to_host(1U, rec, rec_exit);

	/*
	 * The exit to the Host is just a notification; the Host does not need
	 * to complete a PSCI request before the next call to RMI_REC_ENTER.
	 * We therefore update the REC immediately with the results of the PSCI
	 * command.
	 */
	res->smc_res.x[0] = PSCI_RETURN_SUCCESS;
}

static void psci_cpu_off(struct rec *rec, struct rmi_rec_exit *rec_exit,
			 struct rsi_result *res)
{
	res->action = UPDATE_REC_EXIT_TO_HOST;

	/*
	 * It should be fine to set this flag without holding a lock on the
	 * REC or without explicit memory barriers or ordering semantics
	 * operations, because we already ensure that a REC can only be in an
	 * executing state once at any given time, and we're in this execution
	 * context already, and we will be holding a reference count on the
	 * REC at this point, which will be dropped and re-evaluated with
	 * proper barriers before any CPU can evaluate the runnable field
	 * after this change.
	 */
	rec->runnable = false;

	/* Notify the Host, passing the FID only. */
	forward_args_to_host(1U, rec, rec_exit);

	/*
	 * The exit to the Host is just a notification; the Host does not need
	 * to complete a PSCI request before the next call to RMI_REC_ENTER.
	 * We therefore update the REC immediately with the results of the PSCI
	 * command.
	 */
	res->smc_res.x[0] = PSCI_RETURN_SUCCESS;
}

static void psci_reset_rec(struct rec *rec, unsigned long caller_sctlr_el1)
{
	/* Set execution level to EL1 (AArch64) and mask exceptions */
	rec->pstate = SPSR_EL2_MODE_EL1h |
		      SPSR_EL2_nRW_AARCH64 |
		      SPSR_EL2_F_BIT |
		      SPSR_EL2_I_BIT |
		      SPSR_EL2_A_BIT |
		      SPSR_EL2_D_BIT;

	/* Disable stage 1 MMU and caches */
	rec->sysregs.sctlr_el1 = SCTLR_EL1_FLAGS;

	/* Set the endianness of the target to that of the caller */
	rec->sysregs.sctlr_el1 |= caller_sctlr_el1 & SCTLR_ELx_EE_BIT;
}

static unsigned long rd_map_read_rec_count(struct granule *g_rd)
{
	unsigned long rec_count;
	struct rd *rd = buffer_granule_map(g_rd, SLOT_RD);

	assert(rd != NULL);

	rec_count = get_rd_rec_count_unlocked(rd);
	buffer_unmap(rd);
	return rec_count;
}

static void psci_cpu_on(struct rec *rec, struct rmi_rec_exit *rec_exit,
			struct rsi_result *res)
{
	unsigned long target_cpu = rec->regs[1];
	unsigned long entry_point_address = rec->regs[2];
	unsigned long target_rec_idx;

	res->action = UPDATE_REC_RETURN_TO_REALM;

	/* Check that entry_point_address is a Protected Realm Address */
	if (!addr_in_rec_par(rec, entry_point_address)) {
		res->smc_res.x[0] = PSCI_RETURN_INVALID_ADDRESS;
		return;
	}

	/* Get REC index from MPIDR */
	target_rec_idx = mpidr_to_rec_idx(target_cpu);

	/*
	 * Check that the target_cpu is a valid value.
	 * Note that the RMM enforces that the REC are created with
	 * consecutively increasing indexes starting from zero.
	 */
	if (target_rec_idx >= rd_map_read_rec_count(rec->realm_info.g_rd)) {
		res->smc_res.x[0] = PSCI_RETURN_INVALID_PARAMS;
		return;
	}

	/* Check if we're trying to turn ourselves on */
	if (target_rec_idx == rec->rec_idx) {
		res->smc_res.x[0] = PSCI_RETURN_ALREADY_ON;
		return;
	}

	/* Record that a PSCI request is outstanding */
	rec->psci_info.pending = true;

	/*
	 * Notify the Host, passing the FID and MPIDR arguments.
	 * Leave REC registers unchanged; these will be read and updated by
	 * psci_complete_request.
	 */
	forward_args_to_host(2U, rec, rec_exit);
	res->action = EXIT_TO_HOST;
}

static void psci_affinity_info(struct rec *rec, struct rmi_rec_exit *rec_exit,
			       struct rsi_result *res)
{
	unsigned long target_affinity = rec->regs[1];
	unsigned long lowest_affinity_level = rec->regs[2];
	unsigned long target_rec_idx;

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if (lowest_affinity_level != 0UL) {
		res->smc_res.x[0] = PSCI_RETURN_INVALID_PARAMS;
		return;
	}

	/* Get REC index from MPIDR */
	target_rec_idx = mpidr_to_rec_idx(target_affinity);

	/*
	 * Check that the target_affinity is a valid value.
	 * Note that the RMM enforces that the REC are created with
	 * consecutively increasing indexes starting from zero.
	 */
	if (target_rec_idx >= rd_map_read_rec_count(rec->realm_info.g_rd)) {
		res->smc_res.x[0] = PSCI_RETURN_INVALID_PARAMS;
		return;
	}

	/* Check if the vCPU targets itself */
	if (target_rec_idx == rec->rec_idx) {
		res->smc_res.x[0] = PSCI_AFFINITY_INFO_ON;
		return;
	}

	/* Record that a PSCI request is outstanding */
	rec->psci_info.pending = true;

	/*
	 * Notify the Host, passing the FID and MPIDR arguments.
	 * Leave REC registers unchanged; these will be read and updated
	 * by psci_complete_request.
	 */
	forward_args_to_host(2U, rec, rec_exit);

	res->action = EXIT_TO_HOST;
}

/*
 * Turning a system off or requesting a reboot of a realm is enforced by the
 * RMM by preventing execution of a REC after the function has run.  Reboot
 * functionality must be provided by the host hypervisor by creating a new
 * Realm with associated attestation, measurement etc.
 */
static void system_off_reboot(struct rec *rec)
{
	struct rd *rd;
	struct granule *g_rd = rec->realm_info.g_rd;

	/*
	 * The RECs (and, consequently, the PSCI calls) run without any
	 * RMM lock held. Therefore, we cannot cause a deadlock when we acquire
	 * the rd lock here before we set the Realm's new state.
	 */
	granule_lock(g_rd, GRANULE_STATE_RD);
	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	set_rd_state(rd, REALM_SYSTEM_OFF);

	buffer_unmap(rd);
	granule_unlock(g_rd);

	/* TODO: Invalidate all stage 2 entris to ensure REC exits */
}

static void psci_system_off_reset(struct rec *rec,
				  struct rmi_rec_exit *rec_exit,
				  struct rsi_result *res)
{
	system_off_reboot(rec);

	/* Notify the Host, passing the FID only */
	forward_args_to_host(1U, rec, rec_exit);

	res->action = EXIT_TO_HOST;
}

static void psci_features(struct rec *rec, struct rsi_result *res)
{
	unsigned int psci_func_id = (unsigned int)rec->regs[1];

	switch (psci_func_id) {
	case SMC32_PSCI_CPU_SUSPEND:
	case SMC64_PSCI_CPU_SUSPEND:
	case SMC32_PSCI_CPU_OFF:
	case SMC32_PSCI_CPU_ON:
	case SMC64_PSCI_CPU_ON:
	case SMC32_PSCI_AFFINITY_INFO:
	case SMC64_PSCI_AFFINITY_INFO:
	case SMC32_PSCI_SYSTEM_OFF:
	case SMC32_PSCI_SYSTEM_RESET:
	case SMC32_PSCI_FEATURES:
	case SMCCC_VERSION:
		res->smc_res.x[0] = PSCI_RETURN_SUCCESS;
		break;
	default:
		res->smc_res.x[0] = PSCI_RETURN_NOT_SUPPORTED;
	}

	res->action = UPDATE_REC_RETURN_TO_REALM;
}

void handle_psci(struct rec *rec,
		 struct rmi_rec_exit *rec_exit,
		 struct rsi_result *res)
{
	unsigned int function_id = (unsigned int)rec->regs[0];

	switch (function_id) {
	case SMC32_PSCI_VERSION:
		psci_version(res);
		break;
	case SMC32_PSCI_CPU_SUSPEND:
	case SMC64_PSCI_CPU_SUSPEND:
		psci_cpu_suspend(rec, rec_exit, res);
		break;
	case SMC32_PSCI_CPU_OFF:
		psci_cpu_off(rec, rec_exit, res);
		break;
	case SMC32_PSCI_CPU_ON:
	case SMC64_PSCI_CPU_ON:
		psci_cpu_on(rec, rec_exit, res);
		break;
	case SMC32_PSCI_AFFINITY_INFO:
	case SMC64_PSCI_AFFINITY_INFO:
		psci_affinity_info(rec, rec_exit, res);
		break;
	case SMC32_PSCI_SYSTEM_OFF:
	case SMC32_PSCI_SYSTEM_RESET:
		psci_system_off_reset(rec, rec_exit, res);
		break;
	case SMC32_PSCI_FEATURES:
		psci_features(rec, res);
		break;
	default:
		res->action = UPDATE_REC_RETURN_TO_REALM;
		res->smc_res.x[0] = PSCI_RETURN_NOT_SUPPORTED;
		break;
	}

	if (((unsigned int)res->action & FLAG_EXIT_TO_HOST) != 0U) {
		rec_exit->exit_reason = RMI_EXIT_PSCI;
	}
}

/*
 * In the following two functions, it is only safe to access the runnable field
 * on the target_rec once the target_rec is no longer running on another PE and
 * all writes performed by the other PE as part of smc_rec_enter is also
 * guaranteed to be observed here, which we know when we read a zero refcount
 * on the target rec using acquire semantics paired with the release semantics
 * on the reference count in smc_rec_enter. If we observe a non-zero refcount
 * it simply means that the target_rec is running and we can return the
 * corresponding value.
 */
static unsigned long complete_psci_cpu_on(struct rec *target_rec,
					  unsigned long entry_point_address,
					  unsigned long context_id,
					  unsigned long caller_sctlr_el1,
					  unsigned long status)
{
	if ((granule_refcount_read_acquire(target_rec->g_rec) != 0U) ||
		target_rec->runnable) {
		return PSCI_RETURN_ALREADY_ON;
	}

	/*
	 * Host is permitted to deny a PSCI_CPU_ON request,
	 * if the target CPU is not already on.
	 */
	if (status == PSCI_RETURN_DENIED) {
		return PSCI_RETURN_DENIED;
	}

	psci_reset_rec(target_rec, caller_sctlr_el1);
	target_rec->regs[0] = context_id;
	target_rec->pc = entry_point_address;
	target_rec->runnable = true;
	return PSCI_RETURN_SUCCESS;
}

static unsigned long complete_psci_affinity_info(struct rec *target_rec)
{
	if ((granule_refcount_read_acquire(target_rec->g_rec) != 0U) ||
		target_rec->runnable) {
		return PSCI_AFFINITY_INFO_ON;
	}

	return PSCI_AFFINITY_INFO_OFF;
}

unsigned long psci_complete_request(struct rec *calling_rec,
				    struct rec *target_rec, unsigned long status)
{
	unsigned long ret = RMI_SUCCESS;
	unsigned long rec_ret = PSCI_RETURN_NOT_SUPPORTED;
	unsigned long mpidr = calling_rec->regs[1];

	if (!calling_rec->psci_info.pending) {
		return RMI_ERROR_INPUT;
	}

	if (calling_rec->realm_info.g_rd != target_rec->realm_info.g_rd) {
		return RMI_ERROR_INPUT;
	}

	if (mpidr_to_rec_idx(mpidr) != target_rec->rec_idx) {
		return RMI_ERROR_INPUT;
	}

	switch (calling_rec->regs[0]) {
	case SMC32_PSCI_CPU_ON:
	case SMC64_PSCI_CPU_ON:
		if ((status != PSCI_RETURN_SUCCESS) &&
		    (status != PSCI_RETURN_DENIED)) {
			return RMI_ERROR_INPUT;
		}

		rec_ret = complete_psci_cpu_on(target_rec,
						calling_rec->regs[2],
						calling_rec->regs[3],
						calling_rec->sysregs.sctlr_el1,
						status);
		/*
		 * If the target CPU is already running and the Host has denied the
		 * PSCI_CPU_ON request, then return error back to Host.
		 */
		if ((status == PSCI_RETURN_DENIED) &&
		   (rec_ret == PSCI_RETURN_ALREADY_ON)) {
			ret = RMI_ERROR_INPUT;
		}
		break;
	case SMC32_PSCI_AFFINITY_INFO:
	case SMC64_PSCI_AFFINITY_INFO:
		if (status != PSCI_RETURN_SUCCESS) {
			return RMI_ERROR_INPUT;
		}

		rec_ret = complete_psci_affinity_info(target_rec);
		break;
	default:
		assert(false);
	}

	calling_rec->regs[0] = rec_ret;
	calling_rec->regs[1] = 0;
	calling_rec->regs[2] = 0;
	calling_rec->regs[3] = 0;
	calling_rec->psci_info.pending = false;

	return ret;
}

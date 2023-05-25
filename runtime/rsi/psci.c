/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <granule.h>
#include <psci.h>
#include <realm.h>
#include <rec.h>
#include <smc-rmi.h>
#include <smc.h>
#include <stdint.h>

static struct psci_result psci_version(struct rec *rec)
{
	struct psci_result result = { 0 };
	unsigned int version_1_1 = (1U << 16) | 1U;

	result.smc_res.x[0] = (unsigned long)version_1_1;
	return result;
}

static struct psci_result psci_cpu_suspend(struct rec *rec,
					  unsigned long entry_point_address,
					  unsigned long context_id)
{
	struct psci_result result = { 0 };

	/*
	 * We treat all target power states as suspend requests, so all we
	 * need to do is inform that NS hypervisor and we can ignore all the
	 * parameters.
	 */
	result.hvc_forward.forward_psci_call = true;

	result.smc_res.x[0] = PSCI_RETURN_SUCCESS;
	return result;
}

static struct psci_result psci_cpu_off(struct rec *rec)
{
	struct psci_result result = { 0 };

	result.hvc_forward.forward_psci_call = true;

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

	result.smc_res.x[0] = PSCI_RETURN_SUCCESS;
	return result;
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
	struct rd *rd = granule_map(g_rd, SLOT_RD);

	rec_count = get_rd_rec_count_unlocked(rd);
	buffer_unmap(rd);
	return rec_count;
}

static struct psci_result psci_cpu_on(struct rec *rec,
				      unsigned long target_cpu,
				      unsigned long entry_point_address,
				      unsigned long context_id)
{
	struct psci_result result = { 0 };
	unsigned long target_rec_idx;

	/* Check that entry_point_address is a Protected Realm Address */
	if (!addr_in_rec_par(rec, entry_point_address)) {
		result.smc_res.x[0] = PSCI_RETURN_INVALID_ADDRESS;
		return result;
	}

	/* Get REC index from MPIDR */
	target_rec_idx = mpidr_to_rec_idx(target_cpu);

	/*
	 * Check that the target_cpu is a valid value.
	 * Note that the RMM enforces that the REC are created with
	 * consecutively increasing indexes starting from zero.
	 */
	if (target_rec_idx >= rd_map_read_rec_count(rec->realm_info.g_rd)) {
		result.smc_res.x[0] = PSCI_RETURN_INVALID_PARAMS;
		return result;
	}

	/* Check if we're trying to turn ourselves on */
	if (target_rec_idx == rec->rec_idx) {
		result.smc_res.x[0] = PSCI_RETURN_ALREADY_ON;
		return result;
	}

	rec->psci_info.pending = true;

	result.hvc_forward.forward_psci_call = true;
	result.hvc_forward.x1 = target_cpu;
	return result;
}

static struct psci_result psci_affinity_info(struct rec *rec,
					     unsigned long target_affinity,
					     unsigned long lowest_affinity_level)
{
	struct psci_result result = { 0 };
	unsigned long target_rec_idx;

	if (lowest_affinity_level != 0UL) {
		result.smc_res.x[0] = PSCI_RETURN_INVALID_PARAMS;
		return result;
	}

	/* Get REC index from MPIDR */
	target_rec_idx = mpidr_to_rec_idx(target_affinity);

	/*
	 * Check that the target_affinity is a valid value.
	 * Note that the RMM enforces that the REC are created with
	 * consecutively increasing indexes starting from zero.
	 */
	if (target_rec_idx >= rd_map_read_rec_count(rec->realm_info.g_rd)) {
		result.smc_res.x[0] = PSCI_RETURN_INVALID_PARAMS;
		return result;
	}

	/* Check if the vCPU targets itself */
	if (target_rec_idx == rec->rec_idx) {
		result.smc_res.x[0] = PSCI_AFFINITY_INFO_ON;
		return result;
	}

	rec->psci_info.pending = true;

	result.hvc_forward.forward_psci_call = true;
	result.hvc_forward.x1 = target_affinity;
	return result;
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
	rd = granule_map(rec->realm_info.g_rd, SLOT_RD);

	set_rd_state(rd, REALM_STATE_SYSTEM_OFF);

	buffer_unmap(rd);
	granule_unlock(g_rd);

	/* TODO: Invalidate all stage 2 entris to ensure REC exits */
}

static struct psci_result psci_system_off(struct rec *rec)
{
	struct psci_result result = { 0 };

	system_off_reboot(rec);

	result.hvc_forward.forward_psci_call = true;
	return result;
}

static struct psci_result psci_system_reset(struct rec *rec)
{
	struct psci_result result = { 0 };

	system_off_reboot(rec);

	result.hvc_forward.forward_psci_call = true;
	return result;
}

static struct psci_result psci_features(struct rec *rec,
				       unsigned int psci_func_id)
{
	struct psci_result result = { 0 };
	unsigned long ret;

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
		ret = 0UL;
		break;
	default:
		ret = PSCI_RETURN_NOT_SUPPORTED;
	}

	result.smc_res.x[0] = ret;
	return result;
}

struct psci_result psci_rsi(struct rec *rec,
			    unsigned int function_id,
			    unsigned long arg0,
			    unsigned long arg1,
			    unsigned long arg2)
{
	struct psci_result result;

	switch (function_id) {
	case SMC32_PSCI_VERSION:
		result = psci_version(rec);
		break;
	case SMC32_PSCI_CPU_SUSPEND:
	case SMC64_PSCI_CPU_SUSPEND:
		result = psci_cpu_suspend(rec, arg0, arg1);
		break;
	case SMC32_PSCI_CPU_OFF:
		result = psci_cpu_off(rec);
		break;
	case SMC32_PSCI_CPU_ON:
		arg0 = (unsigned int)arg0;
		arg1 = (unsigned int)arg1;
		arg2 = (unsigned int)arg2;
		/* Fall through */
	case SMC64_PSCI_CPU_ON:
		result = psci_cpu_on(rec, arg0, arg1, arg2);
		break;
	case SMC32_PSCI_AFFINITY_INFO:
		arg0 = (unsigned int)arg0;
		arg1 = (unsigned int)arg1;
		FALLTHROUGH;
	case SMC64_PSCI_AFFINITY_INFO:
		result = psci_affinity_info(rec, arg0, arg1);
		break;
	case SMC32_PSCI_SYSTEM_OFF:
		result = psci_system_off(rec);
		break;
	case SMC32_PSCI_SYSTEM_RESET:
		result = psci_system_reset(rec);
		break;
	case SMC32_PSCI_FEATURES:
		result = psci_features(rec, arg0);
		break;
	default:
		result.smc_res.x[0] = PSCI_RETURN_NOT_SUPPORTED;
		result.hvc_forward.forward_psci_call = false;
		break;
	}

	return result;
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
					  unsigned long caller_sctlr_el1)
{
	if ((granule_refcount_read_acquire(target_rec->g_rec) != 0UL) ||
		target_rec->runnable) {
		return PSCI_RETURN_ALREADY_ON;
	}

	psci_reset_rec(target_rec, caller_sctlr_el1);
	target_rec->pc = entry_point_address;
	target_rec->runnable = true;
	return PSCI_RETURN_SUCCESS;
}

static unsigned long complete_psci_affinity_info(struct rec *target_rec)
{
	if ((granule_refcount_read_acquire(target_rec->g_rec) != 0UL) ||
		target_rec->runnable) {
		return PSCI_AFFINITY_INFO_ON;
	}

	return PSCI_AFFINITY_INFO_OFF;
}

unsigned long psci_complete_request(struct rec *calling_rec,
				    struct rec *target_rec)
{
	unsigned long ret = PSCI_RETURN_NOT_SUPPORTED;
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
		ret = complete_psci_cpu_on(target_rec,
					   calling_rec->regs[2],
					   calling_rec->sysregs.sctlr_el1);
		break;
	case SMC32_PSCI_AFFINITY_INFO:
	case SMC64_PSCI_AFFINITY_INFO:
		ret = complete_psci_affinity_info(target_rec);
		break;
	default:
		assert(false);
	}

	calling_rec->regs[0] = ret;
	calling_rec->regs[1] = 0;
	calling_rec->regs[2] = 0;
	calling_rec->regs[3] = 0;
	calling_rec->psci_info.pending = false;

	return RMI_SUCCESS;
}

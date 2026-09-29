/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <firme.h>
#include <rmm_el3_gpi.h>
#include <rmm_el3_ifc.h>
#include <rmm_el3_ifc_priv.h>
#include <spinlock.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <utils_def.h>

#define MEC_REFRESH_MECID_SHIFT		U(32)
#define MEC_REFRESH_MECID_WIDTH		UL(16)

#define MEC_REFRESH_REASON_SHIFT	U(0)
#define MEC_REFRESH_REASON_WIDTH	UL(1)

/* Spinlock used to protect the EL3<->RMM shared area */
static spinlock_t shared_area_lock = {0U};

/*
 * Convert a legacy GTSI SMCCC status to an RMM-EL3 interface status.
 * Unknown legacy values are not exposed to callers.
 */
static int rmm_el3_ifc_gtsi_legacy_status(unsigned long status)
{
	switch (status) {
	case SMC_SUCCESS:
		return E_RMM_OK;
	case SMC_INVALID_PARAMETER:
		return E_RMM_INVAL;
	case SMC_NOT_SUPPORTED:
	default:
		return E_RMM_UNK;
	}
}

/* Helper to detect whether EL3_TOKEN_SIGN is supported by EL3 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
bool rmm_el3_ifc_el3_token_sign_supported(void)
{
	static uint64_t feat_reg;
	static bool feat_reg_read;

	if (!feat_reg_read) {
		int ret;
		ret = rmm_el3_ifc_get_feat_register(RMM_EL3_IFC_FEAT_REG_0_IDX,
						&feat_reg);
		if (ret != 0) {
			ERROR("Failed to get feature register\n");
			return false;
		}

		feat_reg_read = true;
	}

	return (feat_reg & MASK(RMM_EL3_IFC_FEAT_REG_0_EL3_TOKEN_SIGN)) != 0UL;
}

/*
 * Get and lock a pointer to the start of the RMM<->EL3 shared buffer.
 */
/* cppcheck-suppress misra-c2012-8.7 */
uintptr_t rmm_el3_ifc_get_shared_buf_locked(void)
{
	spinlock_acquire(&shared_area_lock);

	return rmm_shared_buffer_start_va;
}

/*
 * Release the RMM <-> EL3 buffer.
 */
/* cppcheck-suppress misra-c2012-8.7 */
void rmm_el3_ifc_release_shared_buf(void)
{
	spinlock_release(&shared_area_lock);
}

static unsigned long get_buffer_pa(uintptr_t buf, size_t buflen)
{
	unsigned long buffer_pa;
	unsigned long offset = buf - rmm_shared_buffer_start_va;

	(void)buflen;

	assert((offset + buflen) <= rmm_el3_ifc_get_shared_buf_size());
	assert((buf & GRANULE_MASK) == rmm_shared_buffer_start_va);

	buffer_pa = (unsigned long)rmm_el3_ifc_get_shared_buf_pa() + offset;

	return buffer_pa;
}

static int rmm_el3_ifc_get_realm_attest_key_internal(uintptr_t buf,
						     size_t buflen, size_t *len,
						     unsigned int crv,
						     unsigned long smc_fid)
{
	struct smc_result smc_res;
	/* cppcheck-suppress misra-c2012-9.3 */
	struct smc_args smc_args = SMC_ARGS_3(get_buffer_pa(buf, buflen), buflen, crv);

	monitor_call_with_arg_res(smc_fid, &smc_args, &smc_res);

	/* coverity[uninit_use:SUPPRESS] */
	if (smc_res.x[0] != 0UL) {
		ERROR("Failed to get realm attestation key x0 = 0x%lx\n",
		      smc_res.x[0]);
		return (int)smc_res.x[0];
	}

	*len = smc_res.x[1];

	return E_RMM_OK;
}

/*
 * Get the realm attestation key to sign the realm attestation token. It is
 * expected that only the private key is retrieved in raw format.
 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
/* cppcheck-suppress misra-c2012-8.7 */
int rmm_el3_ifc_get_realm_attest_key(uintptr_t buf, size_t buflen, size_t *len,
				     unsigned int crv)
{
	return rmm_el3_ifc_get_realm_attest_key_internal(
		buf, buflen, len, crv, SMC_RMM_GET_REALM_ATTEST_KEY);
}

/*
 * Get the platform token from the EL3 firmware.
 * The caller must have already populated the public hash in `buf` which is an
 * input for platform token computation.
 */
/* cppcheck-suppress misra-c2012-8.7 */
int rmm_el3_ifc_get_platform_token(uintptr_t buf, size_t buflen,
					size_t hash_size,
					size_t *token_hunk_len,
					size_t *remaining_len)
{
	struct smc_result smc_res;
	unsigned long rmm_el3_ifc_version = rmm_el3_ifc_get_version();
	/* cppcheck-suppress misra-c2012-9.3 */
	struct smc_args smc_args = SMC_ARGS_3(get_buffer_pa(buf, buflen), buflen, hash_size);

	/* Get the available space on the buffer after the offset */

	monitor_call_with_arg_res(SMC_RMM_GET_PLAT_TOKEN, &smc_args, &smc_res);

	/* coverity[uninit_use:SUPPRESS] */
	if ((long)smc_res.x[0] != 0L) {
		ERROR("Failed to get platform token x0 = 0x%lx\n",
				smc_res.x[0]);
		return (int)smc_res.x[0];
	}

	*token_hunk_len = smc_res.x[1];

	if ((RMM_EL3_IFC_GET_VERS_MAJOR(rmm_el3_ifc_version) == 0U) &&
		(RMM_EL3_IFC_GET_VERS_MINOR(rmm_el3_ifc_version) < 3U)) {
		*remaining_len = 0;
	} else {
		*remaining_len = smc_res.x[2];
	}

	return (int)smc_res.x[0];
}

/*
 * Push an attestation signing request to EL3.
 * The caller must have already populated the request in the shared buffer.
 * The push operation may fail if EL3 does not have enough queue space or if
 * the EL3 is not ready to accept the request.
 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
/* cppcheck-suppress misra-c2012-8.7 */
int rmm_el3_ifc_push_el3_token_sign_request(
	const struct el3_token_sign_request *req)
{
	struct smc_result smc_res;
	/* cppcheck-suppress misra-c2012-9.3 */
	struct smc_args smc_args = SMC_ARGS_3(SMC_RMM_EL3_TOKEN_SIGN_PUSH_REQ_OP,
				    get_buffer_pa((uintptr_t)req, sizeof(*req)), sizeof(*req));

	if (!rmm_el3_ifc_el3_token_sign_supported()) {
		ERROR("EL3 does not support token signing\n");
		return E_RMM_UNK;
	}

	monitor_call_with_arg_res(SMC_RMM_EL3_TOKEN_SIGN, &smc_args, &smc_res);

	/* coverity[uninit_use:SUPPRESS] */
	if (smc_res.x[0] != 0UL) {
		VERBOSE("Failed to push token sign req to EL3 x0 = 0x%lx\n",
		      smc_res.x[0]);
		return (int)smc_res.x[0];
	}

	return E_RMM_OK;
}

/*
 * Pull an attestation response from EL3. The pull operation may fail if
 * the EL3 is  not yet ready to provide a response.
 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
/* cppcheck-suppress misra-c2012-8.7 */
int rmm_el3_ifc_pull_el3_token_sign_response(
	const struct el3_token_sign_response *resp)
{
	struct smc_result smc_res;
	/* cppcheck-suppress misra-c2012-9.3 */
	struct smc_args smc_args = SMC_ARGS_3(SMC_RMM_EL3_TOKEN_SIGN_PULL_RESP_OP,
				    get_buffer_pa((uintptr_t)resp, sizeof(*resp)), sizeof(*resp));

	if (!rmm_el3_ifc_el3_token_sign_supported()) {
		ERROR("EL3 does not support token signing\n");
		return E_RMM_UNK;
	}

	monitor_call_with_arg_res(SMC_RMM_EL3_TOKEN_SIGN, &smc_args, &smc_res);

	/* coverity[uninit_use:SUPPRESS] */
	if (smc_res.x[0] != 0UL) {
		VERBOSE("Failed to get token sign response x0 = 0x%lx\n",
		      smc_res.x[0]);
		return (int)smc_res.x[0];
	}

	return E_RMM_OK;
}

/*
 * Get the realm attestation public key from EL3. This is required when
 * token signing is done in EL3.
 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
/* cppcheck-suppress misra-c2012-8.7 */
int rmm_el3_ifc_get_realm_attest_pub_key_from_el3(uintptr_t buf, size_t buflen,
						  size_t *len, unsigned int crv)
{
	struct smc_result smc_res;
	/* cppcheck-suppress misra-c2012-9.3 */
	struct smc_args smc_args = SMC_ARGS_4(SMC_RMM_EL3_TOKEN_SIGN_GET_RAK_PUB_OP,
				     get_buffer_pa(buf, buflen), buflen, crv);

	if (!rmm_el3_ifc_el3_token_sign_supported()) {
		ERROR("EL3 does not support token signing\n");
		return E_RMM_UNK;
	}

	monitor_call_with_arg_res(SMC_RMM_EL3_TOKEN_SIGN, &smc_args, &smc_res);

	/* coverity[uninit_use:SUPPRESS] */
	if (smc_res.x[0] != 0UL) {
		ERROR("Failed to get realm attestation public key x0 = 0x%lx\n",
		      smc_res.x[0]);
		return (int)smc_res.x[0];
	}

	*len = smc_res.x[1];

	return E_RMM_OK;
}

/*
 * Access the feature register. This is supported for interface version 0.4 and
 * later.
 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
int rmm_el3_ifc_get_feat_register(unsigned int feat_reg_idx, uint64_t *feat_reg)
{
	struct smc_result smc_res;
	/* cppcheck-suppress misra-c2012-9.3 */
	struct smc_args smc_args = SMC_ARGS_1(feat_reg_idx);
	unsigned long rmm_el3_ifc_version = rmm_el3_ifc_get_version();

	/* SMC_RMM_EL3_FEATURES is available from 0.4 */
	if ((RMM_EL3_IFC_GET_VERS_MAJOR(rmm_el3_ifc_version) == 0U) &&
		(RMM_EL3_IFC_GET_VERS_MINOR(rmm_el3_ifc_version) < 4U)) {
		ERROR("Feature register access not supported by this version 0x%lx\n",
			rmm_el3_ifc_version);
		return E_RMM_UNK;
	}

	monitor_call_with_arg_res(SMC_RMM_EL3_FEATURES, &smc_args, &smc_res);

	/* coverity[uninit_use:SUPPRESS] */
	if (smc_res.x[0] != 0UL) {
		ERROR("Failed to get feature register x0 = 0x%lx\n",
		      smc_res.x[0]);
		return (int)smc_res.x[0];
	}

	*feat_reg = smc_res.x[1];

	return E_RMM_OK;
}

/* cppcheck-suppress misra-c2012-8.7 */
unsigned long rmm_el3_ifc_mec_refresh(unsigned short mecid,
					bool is_destroy)
{
	unsigned long x1 = 0UL;

	/* x1[47:32] */
	x1 |= INPLACE(MEC_REFRESH_MECID, mecid);
	/* x1[0] */
	x1 |= INPLACE(MEC_REFRESH_REASON, (unsigned long)is_destroy);

	if (firme_supports_mec_refresh()) {
		return monitor_call(SMC_FIRME_MECID_REFRESH, x1,
					0UL, 0UL, 0UL, 0UL, 0UL);
	}

	return monitor_call(SMC_RMM_MEC_REFRESH, x1,
				0UL, 0UL, 0UL, 0UL, 0UL);
}

/* cppcheck-suppress misra-c2012-8.7 */
int rmm_el3_ifc_reserve_memory(size_t required_size, unsigned int flags,
			       unsigned long alignment, uintptr_t *address)
{
	struct smc_args smc_args __unused;
	struct smc_result smc_res;

	if (alignment < 1UL) {
		return -EINVAL;
	}

	/*
	 * Alignment needs to be a power of 2. We extract the exponent required for such
	 * an alignment.
	 */
	assert(IS_POWER_OF_TWO(alignment));
	uint64_t alignment_exponent = (unsigned long)__builtin_ctzl(alignment);

	/*
	 * The flags and the alignment go into register X2 (the "args" part of the input
	 * to the SMC call). Bit[0] is the local CPU flag and the remaining flags are in
	 * bits[31:1].
	 */
	uint64_t args_value = INPLACE(RESERVE_MEM_ALIGN, alignment_exponent) |
			      ((uint64_t)flags & RESERVE_MEM_FLAG_LOCAL_CPU) |
			      INPLACE(RESERVE_MEM_FLAGS,
				      ((uint64_t)flags >> RESERVE_MEM_FLAGS_SHIFT));

#ifdef RMM_EL3_COMPAT_RESERVE_MEM
	compat_reserve_memory(required_size, args_value, &smc_res);
#else
	smc_args = SMC_ARGS_2(required_size, args_value);
	monitor_call_with_arg_res(SMC_RMM_RESERVE_MEMORY,
			      &smc_args, &smc_res);
#endif

	/* coverity[uninit_use:SUPPRESS] */
	int smc_return_status = (int)smc_res.x[0];
	if (smc_return_status < 0) {
		ERROR("Failed to reserve memory: %d\n", smc_return_status);
		return smc_return_status;
	}

	INFO("Reserve mem: %lu pages at PA: 0x%lx (alignment 0x%lx)\n",
			(unsigned long)(required_size / GRANULE_SIZE),
			smc_res.x[1], alignment);

	*address = smc_res.x[1];
	return 0;
}

/*
 * Delegate [@addr, @addr + @size) through the legacy single-Granule GTSI
 * interface. Stop after a completed Granule if an interrupt is pending, or at
 * the first rejected Granule. Preserve the completed prefix so the caller can
 * apply its tracking policy.
 *
 * @processed_size receives the prefix which remains delegated.
 *
 * Return E_RMM_OK for the completed or interrupted prefix, or the standardized
 * EL3 error even when earlier Granules were successfully delegated.
 */
static int rmm_el3_ifc_gtsi_delegate_legacy(unsigned long addr,
					     unsigned long size,
					     unsigned long *processed_size)
{
	unsigned long offset = 0UL;

	assert(processed_size != NULL);
	*processed_size = 0UL;

	while (offset < size) {
		unsigned long ret;

		ret = monitor_call(SMC_RMM_GTSI_DELEGATE, addr + offset,
				   0UL, 0UL, 0UL, 0UL, 0UL);
		if (ret != SMC_SUCCESS) {
			*processed_size = offset;
			return rmm_el3_ifc_gtsi_legacy_status(ret);
		}
		offset += GRANULE_SIZE;
		/* Yield after progress so E_RMM_OK never reports an empty prefix. */
		if (read_isr_el1() != 0UL) {
			break;
		}
	}

	*processed_size = offset;
	return E_RMM_OK;
}

/*
 * Undelegate [@addr, @addr + @size) through the legacy single-Granule GTSI
 * interface. The caller owns every input Granule in Realm PAS and must retain
 * that ownership until the transition completes.
 *
 * @processed_size receives the size of the successfully undelegated prefix.
 *
 * Return E_RMM_OK after the complete range was undelegated. An EL3 failure
 * violates the ownership contract: log the failing PA and status, then panic.
 */
static int rmm_el3_ifc_gtsi_undelegate_legacy(unsigned long addr,
					       unsigned long size,
					       unsigned long *processed_size)
{
	assert(processed_size != NULL);
	*processed_size = 0UL;

	for (unsigned long offset = 0UL; offset < size;
	     offset += GRANULE_SIZE) {
		unsigned long ret;

		ret = monitor_call(SMC_RMM_GTSI_UNDELEGATE, addr + offset,
				   0UL, 0UL, 0UL, 0UL, 0UL);
		if (ret != SMC_SUCCESS) {
			ERROR("GTSI undelegation failed at 0x%lx: status 0x%lx\n",
			      addr + offset, ret);
			panic();
		}

		*processed_size += GRANULE_SIZE;
	}

	return E_RMM_OK;
}

/*
 * Apply @target_gpi to [@addr, @addr + @size) with one FIRME call.
 *
 * @processed_size receives the size of the stateless prefix processed by the
 * call. FIRME_SUCCESS, FIRME_DENIED, FIRME_INCOMPLETE, FIRME_OP_CONFLICT and
 * FIRME_NOT_FOUND can all report such progress. @cookie receives the stateful
 * operation cookie when FIRME_INCOMPLETE is returned.
 * A success response without progress violates FIRME's result contract:
 * log the failing PA and panic, including when assertions are disabled.
 *
 * Return: The signed W0 FIRME status extended to match the FIRME constants.
 */
static unsigned long rmm_el3_ifc_firme_gpi_set(unsigned long addr,
						unsigned long size,
						unsigned int target_gpi,
						unsigned long *processed_size,
						unsigned long *cookie)
{
	unsigned long granule_count = size / GRANULE_SIZE;
	struct smc_result smc_res;
	/* cppcheck-suppress misra-c2012-9.3 */
	struct smc_args smc_args = SMC_ARGS_3(addr, granule_count, target_gpi);
	unsigned long ret;
	unsigned long processed_count;

	assert((processed_size != NULL) && (cookie != NULL));
	*processed_size = 0UL;

	monitor_call_with_arg_res(SMC_FIRME_GM_GPI_SET, &smc_args, &smc_res);
	/* FIRME defines a signed 32-bit status; the upper X0 bits are ignored. */
	ret = (unsigned long)(int32_t)smc_res.x[0];
	if ((ret != FIRME_SUCCESS) && (ret != FIRME_DENIED) &&
	    (ret != FIRME_INCOMPLETE) &&
	    (ret != FIRME_OP_CONFLICT) && (ret != FIRME_NOT_FOUND)) {
		return ret;
	}

	processed_count = smc_res.x[1];
	assert(processed_count <= granule_count);
	/* FIRME SUCCESS requires progress, but can leave a stateless suffix. */
	if ((ret == FIRME_SUCCESS) && (processed_count == 0UL)) {
		ERROR("FIRME GPI_SET succeeded without progress at 0x%lx\n", addr);
		panic();
	}

	/* The other accepted statuses must leave at least one Granule unprocessed. */
	assert((ret == FIRME_SUCCESS) || (processed_count < granule_count));
	*processed_size = processed_count * GRANULE_SIZE;
	if (ret == FIRME_INCOMPLETE) {
		*cookie = smc_res.x[2];
	}
	return ret;
}

/*
 * Resume the FIRME GPI transition identified by @cookie.
 *
 * A valid Granule count is returned for statuses which end a stateful phase
 * or pause it again with FIRME_INCOMPLETE. FIRME_BUSY reports no progress but
 * retains the existing operation; use its returned cookie for the next call.
 * Other statuses have no valid outputs.
 * A success response without progress is logged with its cookie and causes
 * a panic, including when assertions are disabled.
 * Return the signed W0 FIRME status extended to match the FIRME constants.
 */
static unsigned long rmm_el3_ifc_firme_gpi_continue(
						unsigned long cookie,
						unsigned long remaining_size,
						unsigned long *processed_size,
						unsigned long *next_cookie)
{
	unsigned long granule_count = remaining_size / GRANULE_SIZE;
	struct smc_result smc_res;
	/* cppcheck-suppress misra-c2012-9.3 */
	struct smc_args smc_args = SMC_ARGS_1(cookie);
	unsigned long ret;

	assert((remaining_size != 0UL) && GRANULE_ALIGNED(remaining_size) &&
	       (processed_size != NULL) && (next_cookie != NULL));
	(void)granule_count;
	*processed_size = 0UL;

	monitor_call_with_arg_res(SMC_FIRME_GM_GPI_OP_CONTINUE,
				  &smc_args, &smc_res);
	/* FIRME defines a signed 32-bit status; the upper X0 bits are ignored. */
	ret = (unsigned long)(int32_t)smc_res.x[0];
	if ((ret == FIRME_SUCCESS) || (ret == FIRME_DENIED) ||
	    (ret == FIRME_INCOMPLETE) || (ret == FIRME_OP_CONFLICT) ||
	    (ret == FIRME_NOT_FOUND)) {
		unsigned long processed_count = smc_res.x[1];

		assert(processed_count <= granule_count);
		/* FIRME requires SUCCESS to report at least one processed Granule. */
		if ((ret == FIRME_SUCCESS) && (processed_count == 0UL)) {
			ERROR("FIRME GPI_OP_CONTINUE succeeded without progress: cookie 0x%lx\n",
			      cookie);
			panic();
		}
		assert((ret != FIRME_INCOMPLETE) ||
		       (processed_count < granule_count));
		*processed_size = processed_count * GRANULE_SIZE;
	}
	if ((ret == FIRME_INCOMPLETE) || (ret == FIRME_BUSY)) {
		*next_cookie = smc_res.x[2];
	}

	return ret;
}

/*
 * Enforce the result contract for an undelegation request.
 *
 * RMM owns the input Granules and validates the request parameters. EL3 can
 * therefore make progress, retain the operation, or ask RMM to retry, but it
 * cannot conflict with another operation or reject the request. Check both
 * the initial request and continuation, before publishing progress or state.
 */
static void rmm_el3_ifc_gtsi_assert_undelegate_status(
						int status __unused,
						unsigned long processed_size __unused)
{
	assert(((status == E_RMM_OK) && (processed_size > 0UL)) ||
	       (status == E_RMM_IN_PROGRESS) ||
	       ((status == E_RMM_BUSY) && (processed_size == 0UL)));
}

/*
 * Delegate the Granule-aligned range [@addr, @addr + @size) to Realm PAS.
 *
 * Args:
 *	- addr:	Base PA of the range. Must be Granule-aligned.
 *	- size:	Size of the range in bytes. Must be a nonzero multiple of
 *		GRANULE_SIZE.
 *	- processed_size:	Receives the delegated prefix in bytes, independently
 *				of the returned status. Zero if EL3 supplies no valid
 *				progress count.
 *	- cookie:		Receives the FIRME cookie only on E_RMM_IN_PROGRESS.
 *				Unchanged otherwise; no continuation cookie is valid.
 *
 * FIRME is invoked once. The legacy GTSI interface is invoked once per Granule
 * until completion, error or a pending interrupt. Both preserve any delegated
 * prefix alongside the mapped EL3 status. The caller retains ownership of the
 * range and decides whether its tracking granularity permits reporting
 * progress, requires a suffix retry, or requires rollback after a conflict
 * or permanent failure.
 *
 * Return:
 *	- E_RMM_OK: EL3 processed a non-empty prefix, possibly smaller than @size.
 *	- E_RMM_IN_PROGRESS: FIRME retained a stateful operation and returned a
 *			     cookie. The prefix may be empty.
 *	- E_RMM_AGAIN: FIRME reported a stateless conflict, possibly with progress.
 *		       Any retry of the suffix must use GPI_SET.
 *	- E_RMM_BUSY: EL3 made no progress and retained no stateful operation.
 *	- E_RMM_UNK, E_RMM_BAD_ADDR, E_RMM_BAD_PAS, E_RMM_NOMEM, E_RMM_INVAL,
 *	  E_RMM_FAULT, E_RMM_NOTSUP or E_RMM_DENIED:
 *	  EL3 rejected the operation. @processed_size may still be nonzero.
 */
static int rmm_el3_ifc_gtsi_delegate(unsigned long addr,
				   unsigned long size,
				   unsigned long *processed_size,
				   unsigned long *cookie)
{
	assert(GRANULE_ALIGNED(addr) && (size != 0UL) && GRANULE_ALIGNED(size) &&
	       (processed_size != NULL) && (cookie != NULL));
	*processed_size = 0UL;
	if (firme_supports_gpi_set()) {
		unsigned long ret;

		ret = rmm_el3_ifc_firme_gpi_set(addr, size, GPT_GPI_REALM,
						 processed_size, cookie);
		return firme_errno_to_rmm_errno(ret);
	}

	return rmm_el3_ifc_gtsi_delegate_legacy(addr, size, processed_size);
}

/*
 * Undelegate the granule-aligned range [@addr, @addr + @size) to NS PAS.
 *
 * Args:
 *	- addr:	Base PA of the range. Must be Granule-aligned.
 *	- size:	Size of the range in bytes. Must be a nonzero multiple of
 *		GRANULE_SIZE.
 *	- processed_size:	Receives the size of the prefix changed to NS PAS.
 *	- cookie:		Receives the FIRME cookie when the operation is
 *				incomplete. Unchanged for the legacy interface.
 *
 * At most one FIRME call is issued, allowing the caller to yield after a
 * stateless partial response or retain a cookie for stateful continuation. The
 * legacy GTSI interface is invoked once per Granule until completion. Any
 * legacy failure is logged and causes a panic.
 *
 * Return:
 *	- E_RMM_OK: EL3 processed a non-empty prefix.
 *	- E_RMM_IN_PROGRESS: FIRME retained a stateful operation and returned a
 *			     cookie.
 *	- E_RMM_BUSY: FIRME made no progress; the caller can retry the request.
 *
 * RMM owns every input Granule and validates the range before this call.
 * Therefore, any other EL3 status is an interface contract violation.
 */
static int rmm_el3_ifc_gtsi_undelegate(unsigned long addr,
				     unsigned long size,
				     unsigned long *processed_size,
				     unsigned long *cookie)
{
	int ret;

	assert(GRANULE_ALIGNED(addr) && (size != 0UL) && GRANULE_ALIGNED(size) &&
	       (processed_size != NULL) && (cookie != NULL));
	if (firme_supports_gpi_set()) {
		unsigned long firme_ret;

		firme_ret = rmm_el3_ifc_firme_gpi_set(addr, size, GPT_GPI_NS,
						       processed_size, cookie);
		ret = firme_errno_to_rmm_errno(firme_ret);
	} else {
		ret = rmm_el3_ifc_gtsi_undelegate_legacy(addr, size,
							 processed_size);
	}

	return ret;
}

/*
 * Resume a stateful FIRME GPI transition identified by @cookie.
 *
 * @remaining_size is the Granule-aligned size which has not yet been
 * processed by the operation.
 * @processed_size receives the number of bytes processed by this invocation.
 * @next_cookie receives the returned cookie when FIRME returns INCOMPLETE
 * or BUSY. BUSY retains the existing operation and adds no progress; its
 * UNKNOWN count is ignored.
 *
 * Return:
 *	- E_RMM_OK: FIRME ended the operation after processing a non-empty
 *		    prefix. The prefix may be smaller than @remaining_size; no
 *		    continuation cookie is retained in this case.
 *	- E_RMM_IN_PROGRESS: FIRME retained the operation and returned a new
 *			     cookie.
 *	- E_RMM_BUSY: FIRME made no progress and returned a cookie for the retained
 *		      operation. Use it for another GPI_OP_CONTINUE.
 *	- E_RMM_AGAIN: FIRME reported a conflict and invalidated the cookie.
 *		       Retain @processed_size; any retry of the suffix uses
 *		       GPI_SET after yielding.
 *	- E_RMM_UNK, E_RMM_INVAL, E_RMM_NOTSUP or E_RMM_DENIED:
 *	  Standardized reason that FIRME stopped processing. @processed_size may
 *	  still describe a non-empty prefix.
 */
static int rmm_el3_ifc_gtsi_continue(unsigned long cookie,
				   unsigned long remaining_size,
				   unsigned long *processed_size,
				   unsigned long *next_cookie)
{
	unsigned long ret;

	assert(firme_supports_gpi_set());
	ret = rmm_el3_ifc_firme_gpi_continue(cookie, remaining_size,
						 processed_size, next_cookie);
	return firme_errno_to_rmm_errno(ret);
}

/*
 * Advance one PAS transition and retain its progress and continuation state.
 * Enforce the owned-range result contract for every undelegation step,
 * including EL3 continuations and rollback of an unsuccessful delegation.
 */
/* cppcheck-suppress misra-c2012-8.7 */
int rmm_el3_ifc_gtsi_step(unsigned long addr, unsigned long size, bool delegate,
			unsigned long *processed_size, struct rmm_el3_gpi_state *state)
{
	unsigned long remaining;
	unsigned long progress;
	unsigned long next_cookie = 0UL;
	int ret;

	assert((processed_size != NULL) && (state != NULL));
	assert(GRANULE_ALIGNED(addr) && GRANULE_ALIGNED(size) &&
	       GRANULE_ALIGNED(*processed_size) && (*processed_size < size) &&
	       ((addr + size) > addr));
	remaining = size - *processed_size;

	if (state->incomplete) {
		ret = rmm_el3_ifc_gtsi_continue(state->cookie, remaining,
					      &progress, &next_cookie);
	} else if (delegate) {
		ret = rmm_el3_ifc_gtsi_delegate(addr + *processed_size, remaining,
					      &progress, &next_cookie);
	} else {
		ret = rmm_el3_ifc_gtsi_undelegate(addr + *processed_size, remaining,
						&progress, &next_cookie);
	}

	if (!delegate) {
		rmm_el3_ifc_gtsi_assert_undelegate_status(ret, progress);
	}

	assert((progress <= remaining) && GRANULE_ALIGNED(progress));
	*processed_size += progress;
	state->incomplete = (ret == E_RMM_IN_PROGRESS) ||
			   (state->incomplete && (ret == E_RMM_BUSY));
	state->cookie = state->incomplete ? next_cookie : 0UL;
	return ret;
}

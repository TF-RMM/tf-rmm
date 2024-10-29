/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <rmm_el3_ifc.h>
#include <rmm_el3_ifc_priv.h>
#include <spinlock.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <xlat_defs.h>

/* Spinlock used to protect the EL3<->RMM shared area */
static spinlock_t shared_area_lock = {0U};

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
uintptr_t rmm_el3_ifc_get_shared_buf_locked(void)
{
	spinlock_acquire(&shared_area_lock);

	return rmm_shared_buffer_start_va;
}

/*
 * Release the RMM <-> EL3 buffer.
 */
void rmm_el3_ifc_release_shared_buf(void)
{
	spinlock_release(&shared_area_lock);
}

static unsigned long get_buffer_pa(uintptr_t buf, size_t buflen)
{
	unsigned long buffer_pa;
	unsigned long offset = buf - rmm_shared_buffer_start_va;

	assert((offset + buflen) <= rmm_el3_ifc_get_shared_buf_size());
	assert((buf & ~PAGE_SIZE_MASK) == rmm_shared_buffer_start_va);

	buffer_pa = (unsigned long)rmm_el3_ifc_get_shared_buf_pa() + offset;

	return buffer_pa;
}

static int rmm_el3_ifc_get_realm_attest_key_internal(uintptr_t buf,
						     size_t buflen, size_t *len,
						     unsigned int crv,
						     unsigned long smc_fid)
{
	struct smc_result smc_res;

	monitor_call_with_res(smc_fid,
			      get_buffer_pa(buf, buflen),
			      buflen,
			      crv, 0UL, 0UL, 0UL, &smc_res);

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
int rmm_el3_ifc_get_platform_token(uintptr_t buf, size_t buflen,
					size_t hash_size,
					size_t *token_hunk_len,
					size_t *remaining_len)
{
	struct smc_result smc_res;
	unsigned long rmm_el3_ifc_version = rmm_el3_ifc_get_version();

	/* Get the available space on the buffer after the offset */

	monitor_call_with_res(SMC_RMM_GET_PLAT_TOKEN,
			      get_buffer_pa(buf, buflen),
			      buflen,
			      hash_size,
			      0UL, 0UL, 0UL, &smc_res);

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
int rmm_el3_ifc_push_el3_token_sign_request(
	const struct el3_token_sign_request *req)
{
	struct smc_result smc_res;

	if (!rmm_el3_ifc_el3_token_sign_supported()) {
		ERROR("EL3 does not support token signing\n");
		return E_RMM_UNK;
	}

	monitor_call_with_res(SMC_RMM_EL3_TOKEN_SIGN,
			      SMC_RMM_EL3_TOKEN_SIGN_PUSH_REQ_OP,
			      get_buffer_pa((uintptr_t)req, sizeof(*req)),
			      sizeof(*req),
			      0UL, 0UL, 0UL, &smc_res);

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
int rmm_el3_ifc_pull_el3_token_sign_response(
	const struct el3_token_sign_response *resp)
{
	struct smc_result smc_res;

	if (!rmm_el3_ifc_el3_token_sign_supported()) {
		ERROR("EL3 does not support token signing\n");
		return E_RMM_UNK;
	}

	monitor_call_with_res(SMC_RMM_EL3_TOKEN_SIGN,
			      SMC_RMM_EL3_TOKEN_SIGN_PULL_RESP_OP,
			      get_buffer_pa((uintptr_t)resp, sizeof(*resp)),
			      sizeof(*resp),
			      0UL, 0UL, 0UL, &smc_res);

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
int rmm_el3_ifc_get_realm_attest_pub_key_from_el3(uintptr_t buf, size_t buflen,
						  size_t *len, unsigned int crv)
{
	struct smc_result smc_res;

	if (!rmm_el3_ifc_el3_token_sign_supported()) {
		ERROR("EL3 does not support token signing\n");
		return E_RMM_UNK;
	}

	monitor_call_with_res(SMC_RMM_EL3_TOKEN_SIGN,
			      SMC_RMM_EL3_TOKEN_SIGN_GET_RAK_PUB_OP,
			      get_buffer_pa(buf, buflen),
			      buflen,
			      crv, 0UL, 0UL, &smc_res);

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
	unsigned long rmm_el3_ifc_version = rmm_el3_ifc_get_version();

	if ((RMM_EL3_IFC_GET_VERS_MAJOR(rmm_el3_ifc_version) != 0U) ||
		(RMM_EL3_IFC_GET_VERS_MINOR(rmm_el3_ifc_version) < 4U)) {
		ERROR("Feature register access not supported by this version 0x%lx\n",
			rmm_el3_ifc_version);
		return E_RMM_UNK;
	}

	monitor_call_with_res(SMC_RMM_EL3_FEATURES,
			      feat_reg_idx,
			      0UL, 0UL, 0UL, 0UL, 0UL, &smc_res);

	/* coverity[uninit_use:SUPPRESS] */
	if (smc_res.x[0] != 0UL) {
		ERROR("Failed to get feature register x0 = 0x%lx\n",
		      smc_res.x[0]);
		return (int)smc_res.x[0];
	}

	*feat_reg = smc_res.x[1];

	return E_RMM_OK;
}

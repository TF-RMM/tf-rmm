/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <bitmap.h>
#include <debug.h>
#include <errno.h>
#include <rmm_el3_ifc.h>
#include <rmm_el3_ifc_priv.h>
#include <spinlock.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define MEC_REFRESH_MECID_SHIFT		U(32)
#define MEC_REFRESH_MECID_WIDTH		UL(16)

#define MEC_REFRESH_REASON_SHIFT	U(0)
#define MEC_REFRESH_REASON_WIDTH	UL(1)

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

	if ((RMM_EL3_IFC_GET_VERS_MAJOR(rmm_el3_ifc_version) != 0U) ||
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

	return monitor_call(SMC_RMM_MEC_REFRESH, x1,
				0UL, 0UL, 0UL, 0UL, 0UL);
}

/* cppcheck-suppress misra-c2012-8.7 */
int rmm_el3_ifc_reserve_memory(size_t size, unsigned int flags,
			       unsigned long alignment, uintptr_t *address)
{
	struct smc_args smc_args;
	struct smc_result smc_res;
	uint64_t flags_align;
	int ret;

	if (alignment < 1UL) {
		return -EINVAL;
	}

	/* alignment needs to be a power of 2 */
	flags_align = bitmap_find_next_set_bit(alignment, 0);
	assert((1UL << flags_align) == alignment);

	/* The flags and the alignment go into the second argument. */
	flags_align = INPLACE(RESERVE_MEM_ALIGN, flags_align) |
		      INPLACE(RESERVE_MEM_FLAGS, flags);

	smc_args = SMC_ARGS_2(size, flags_align);
	monitor_call_with_arg_res(SMC_RMM_RESERVE_MEMORY,
			      &smc_args, &smc_res);

	/* coverity[uninit_use:SUPPRESS] */
	ret = (int)smc_res.x[0];
	if (ret < 0) {
		ERROR("Failed to reserve memory: %d\n", ret);
		return ret;
	}

	INFO("Reserve mem: %lu pages at PA: 0x%lx (alignment 0x%lx)\n",
			(unsigned long)(size / GRANULE_SIZE), smc_res.x[1], alignment);

	*address = smc_res.x[1];
	return 0;
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_common.h>
#include <assert.h>
#include <attestation.h>
#include <attestation_priv.h>
#include <attestation_token.h>
#include <debug.h>
#include <el0_app_helpers.h>
#include <errno.h>
#include <psa/crypto.h>
#include <t_cose_el3_token_sign.h>

#if ATTEST_EL3_TOKEN_SIGN
static int el3_token_sign_queue_try_enqueue(struct t_cose_el3_token_sign_ctx *ctx_locked,
					    uint64_t *ticket)
{
	unsigned long ret;
	struct service_el3_token_sign_request *request =
		(struct service_el3_token_sign_request *)get_shared_mem_start();


	if ((ctx_locked == NULL) || (ticket == NULL) ||
		/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
		/* coverity[misra_c_2012_rule_12_1_violation:SUPPRESS] */
		(ctx_locked->state.hash_len > sizeof(request->hash_buf)) ||
		(ctx_locked->state.sign_alg_id != PSA_ALG_ECDSA(PSA_ALG_SHA_384)) ||
		(ctx_locked->state.hash_len != PSA_HASH_LENGTH(PSA_ALG_SHA_384))) {
		return -EINVAL;
	}

	request->cookie = ctx_locked->state.cookie;
	request->hash_buf_len = ctx_locked->state.hash_len;

	memcpy(request->hash_buf,
		ctx_locked->state.hash_buffer,
		ctx_locked->state.hash_len);

	ret = el0_app_service_call(APP_SERVICE_EL3_TOKEN_SIGN_QUEUE_TRY_ENQUEUE,
				   0, 0, 0, 0);
	*ticket = request->ticket;
	return ret;

}

/*
 * Initialize the EL3 token signing module. Also initialize callbacks
 * in the t_cose library. The function returns 0 on success, and -ENOTSUP
 * on failure.
 */
static int el3_token_sign_queue_init(void)
{
	/*
	 * The t_cose layer is initialized first so that even if EL3 firmware
	 * does not support EL3_TOKEN_SIGN, the t_cose layer has a clean state.
	 */
	t_cose_crypto_el3_enqueue_cb_init(el3_token_sign_queue_try_enqueue);

	bool el3_token_sign_supported =
		el0_app_service_call(APP_SERVICE_EL3_IFC_EL3_TOKEN_SIGN_SUPPORTED, 0, 0, 0, 0);

	if (!el3_token_sign_supported) {
		ERROR("The EL3_TOKEN_SIGN feature is not supported by EL3 firmware.");
		return -ENOTSUP;
	}

	return 0;
}

/*
 * Write the response from EL3 to the context. The response is written only if the context
 * is valid and the response is for the right request.
 * The caller must ensure that the REC granule lock is held so that it cannot be deleted
 * while the response is being written.
 * Since the REC granule lock is held, the lock ordering is granule lock -> ctx->lock.
 */
int app_attest_el3_token_write_response_to_ctx(struct token_sign_cntxt *sign_ctx,
					   uint64_t req_ticket,
					   size_t sig_len,
					   uint8_t signature_buf[])
{
	assert(sign_ctx != NULL);

	struct t_cose_el3_token_sign_ctx *ctx = &(sign_ctx->ctx.crypto_ctx);

	spinlock_acquire(&ctx->lock);

	/*
	 * Check the ticket to ensure that the response is for the right
	 * request. If the ticket does not match, drop the response.
	 * The ticket may not match if the request was cancelled by
	 * the realm calling token_init again. It is also possible that
	 * the realm has cancelled an existing request, initialized another
	 * request and  queued it, before the response to the previous request
	 * arrives. The ticket value ensures unique match of request and
	 * response regardless of the number of time, cancel and/or queueing
	 * of requests occur.
	 */
	if ((ctx->state.req_ticket) != (req_ticket)) {
		assert((ctx->state.req_ticket == 0UL) ||
			(ctx->state.req_ticket >= req_ticket));
		ERROR("%s:%d ticket mismatch %lx %lx, dropping response\n",
			__func__, __LINE__, ctx->state.req_ticket,
			req_ticket);
		goto out_buf_lock;
	}

	if (sig_len > ctx->state.sig_len) {
		ERROR("%s:%d sig len mismatch %lx %lx\n", __func__, __LINE__,
		      ctx->state.sig_len, sig_len);
		ctx->state.is_el3_err = true;
		goto out_buf_lock;
	}

	ctx->state.sig_len = sig_len;
	(void)memcpy(ctx->state.sig_buffer,
		(void *)signature_buf, sig_len);
	ctx->state.is_sig_valid = true;

out_buf_lock:
	spinlock_release(&ctx->lock);
	return 0;
}
#endif

int attestation_init(void)
{
	int ret;
	/* Retrieve the platform key from root world */
	ret = attest_init_realm_attestation_key();
	if (ret != 0) {
		return ret;
	}

	/* Retrieve the platform token from root world */
	ret = attest_setup_platform_token();
	if (ret != 0) {
		return ret;
	}

#if ATTEST_EL3_TOKEN_SIGN
	/* Initialize the EL3 queue */
	if (el3_token_sign_queue_init() != 0) {
		WARN("EL3 queue init failed.\n");
		ret = -ENOTSUP;
		return ret;
	}
#endif
	return 0;
}

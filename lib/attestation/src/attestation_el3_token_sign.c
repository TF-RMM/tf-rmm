/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <atomics.h>
#include <attestation_priv.h>
#include <attestation_token.h>
#include <cpuid.h>
#include <debug.h>
#include <errno.h>
#include <rmm_el3_ifc.h>
#include <spinlock.h>
#include <stdbool.h>
#include <string.h>
#include <t_cose_el3_token_sign.h>

static uint64_t el3_token_sign_ticket = 1;

static struct el3_token_sign_response token_sign_response[MAX_CPUS] = { 0 };

/*
 * Callback is called with lock held for the context and imposes lock ordering.
 * Since this function holds the lock for the shared buffer, the lock ordering
 * ctx->lock -> rmm_el3_ifc_get_shared_buf_locked() is expected to be followed.
 * attest_el3_token_write_response_to_ctx() is called with the lock held for a
 * given REC granule and imposes lock ordering of granule lock -> ctx->lock.
 */
static int el3_token_sign_queue_try_enqueue(struct t_cose_el3_token_sign_ctx *ctx_locked,
					 uint64_t *ticket)
{
	int ret = 0;
	struct el3_token_sign_request *req;

	if ((ctx_locked == NULL) || (ticket == NULL) ||
		(ctx_locked->state.hash_len > sizeof(req->hash_buf)) ||
		(ctx_locked->state.sign_alg_id != PSA_ALG_ECDSA(PSA_ALG_SHA_384)) ||
		/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
		/* coverity[misra_c_2012_rule_12_1_violation:SUPPRESS] */
		(ctx_locked->state.hash_len != PSA_HASH_LENGTH(PSA_ALG_SHA_384))) {
		return -EINVAL;
	}

	req = (struct el3_token_sign_request *)rmm_el3_ifc_get_shared_buf_locked();
	/* TODO: For now only ECC_SECP384 is supported */
	req->sign_alg_id = ATTEST_KEY_CURVE_ECC_SECP384R1;
	req->cookie = (uint64_t)ctx_locked->state.cookie;
	/* TODO: For now only SHA384 is supported */
	req->hash_alg_id = EL3_TOKEN_SIGN_HASH_ALG_SHA384;
	(void)memcpy((void *)(req->hash_buf), ctx_locked->state.hash_buffer,
		ctx_locked->state.hash_len);

	/*
	 * Overflow of the 64 bit number will occur after ~580 years at
	 * 1 ns resolution. Even if it does overflow, the ticket will be
	 * 0 and is still valid. Overflow is not expected to be a problem.
	 */
	req->req_ticket = atomic_load_add_64(&el3_token_sign_ticket, 1);
	*ticket = req->req_ticket;

	ret = rmm_el3_ifc_push_el3_token_sign_request(req);

	rmm_el3_ifc_release_shared_buf();

	if (ret == E_RMM_AGAIN) {
		VERBOSE("EL3 asked to retry push\n");
		return -EAGAIN;
	}

	/* Fatal error, unable to push to EL3. */
	if (ret != 0) {
		ERROR("%s: rmm_el3_ifc_push_el3_token_sign_request failed with error %d\n",
		       __func__, ret);
		return -EPERM;
	}

	return 0;
}

int el3_token_sign_queue_init(void)
{
	/*
	 * The t_cose layer is initialized first so that even if EL3 firmware
	 * does not support EL3_TOKEN_SIGN, the t_cose layer has a clean state.
	 */
	t_cose_crypto_el3_enqueue_cb_init(el3_token_sign_queue_try_enqueue);

	if (rmm_el3_ifc_el3_token_sign_supported() == false) {
		ERROR("The EL3_TOKEN_SIGN feature is not supported by EL3 firmware.");
		return -ENOTSUP;
	}

	return 0;
}

/*
 * Pull the response from EL3 into the per cpu response buffer. The function
 * returns the cookie associated with the response that was received.
 */
int attest_el3_token_sign_pull_response_from_el3(uintptr_t *cookie)
{
	uintptr_t shared_buf;
	int ret = 0;
	struct el3_token_sign_response *el3_resp = &token_sign_response[my_cpuid()];

	assert(cookie != NULL);

	shared_buf = rmm_el3_ifc_get_shared_buf_locked();
	ret = rmm_el3_ifc_pull_el3_token_sign_response(
		(const struct el3_token_sign_response *)shared_buf);
	if (ret == E_RMM_AGAIN) {
		VERBOSE("EL3 asked to retry pull\n");
		rmm_el3_ifc_release_shared_buf();
		return -EAGAIN;
	}

	if (ret != E_RMM_OK) {
		ERROR("%s:%d Failed to pull response from EL3: %d\n",
			__func__, __LINE__, ret);
		return -ENOTSUP;
	}

	(void)memcpy((void *)el3_resp, (void *)shared_buf, sizeof(*el3_resp));
	rmm_el3_ifc_release_shared_buf();
	*cookie = (uintptr_t)el3_resp->cookie;

	return 0;
}

/*
 * Write the response from EL3 to the context. The response is written only if the context
 * is valid and the response is for the right request. If the function returns an error
 * the caller must treat it as a fatal error. The cookie is checked against the per cpu
 * response buffer to ensure that the response is for the right request.
 * The caller must ensure that the REC granule lock is held so that it cannot be deleted
 * while the response is being written.
 * Since the REC granule lock is held, the lock ordering is granule lock -> ctx->lock.
 */
int attest_el3_token_write_response_to_ctx(struct token_sign_cntxt *sign_ctx,
					   uintptr_t cookie)
{
	struct el3_token_sign_response *el3_resp = &token_sign_response[my_cpuid()];

	assert(sign_ctx != NULL);

	if ((uint64_t)cookie != el3_resp->cookie) {
		VERBOSE("Response for REC granule %lx not found\n",
			 el3_resp->cookie);
		return -EINVAL;
	}

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
	if ((ctx->state.req_ticket) != (el3_resp->req_ticket)) {
		assert((ctx->state.req_ticket == 0UL) ||
			(ctx->state.req_ticket >= el3_resp->req_ticket));
		ERROR("%s:%d ticket mismatch %lx %lx, dropping response\n",
			__func__, __LINE__, ctx->state.req_ticket,
			el3_resp->req_ticket);
		goto out_buf_lock;
	}

	if (el3_resp->sig_len > ctx->state.sig_len) {
		ERROR("%s:%d sig len mismatch %lx %x\n", __func__, __LINE__,
		      ctx->state.sig_len, el3_resp->sig_len);
		ctx->state.is_el3_err = true;
		goto out_buf_lock;
	}

	ctx->state.sig_len = el3_resp->sig_len;
	(void)memcpy(ctx->state.sig_buffer,
		(void *)el3_resp->signature_buf, el3_resp->sig_len);
	ctx->state.is_sig_valid = true;

out_buf_lock:
	spinlock_release(&ctx->lock);
	return 0;
}

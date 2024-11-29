/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 * This file contains alternative implementations of the signing related
 * functions defined in the t_cose crypto adaption layer.
 * Instead of calling the PSA crypto interface, these implementations use EL3
 * services to perform the signing operation.
 *
 * These functions are called from the patched
 * ext/t_cose/crypto_adapters/t_cose_psa_crypto.c file.
 *
 * For signing, we only use restartable signing since it allows returning
 * to the caller without completing signing, which is required for
 * offloading signing operations to EL3 services, asynchronously.
 */
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <t_cose_crypto.h> /* The interface this implements */
#include <t_cose_el3_token_sign.h>

static t_cose_crypto_el3_enqueue_t t_cose_crypto_el3_enqueue;
static bool cb_initialized;

static void
t_cose_crypto_init_el3_ctx_crypto(struct t_cose_el3_token_sign_ctx *el3_ctx_locked,
				  psa_algorithm_t psa_algorithm_id,
				  struct q_useful_buf_c hash_to_sign,
				  struct q_useful_buf signature_buffer)
{
	/* Assumes lock is held for context */
	el3_ctx_locked->state.sign_alg_id = psa_algorithm_id;
	el3_ctx_locked->state.sig_len = signature_buffer.len;
	el3_ctx_locked->state.sig_buffer = signature_buffer.ptr;
	el3_ctx_locked->state.hash_len = hash_to_sign.len;
	el3_ctx_locked->state.hash_buffer = hash_to_sign.ptr;
}

void t_cose_crypto_el3_enqueue_cb_init(t_cose_crypto_el3_enqueue_t enqueue)
{
	t_cose_crypto_el3_enqueue = enqueue;
	cb_initialized = true;
}

void t_cose_crypto_el3_ctx_init(struct t_cose_el3_token_sign_ctx *el3_ctx,
				uintptr_t cookie)
{
	assert(cb_initialized);

	spinlock_acquire(&el3_ctx->lock);
	(void)memset(&el3_ctx->state, 0, sizeof(el3_ctx->state));
	el3_ctx->state.cookie = cookie;
	spinlock_release(&el3_ctx->lock);
}

/*
 * See documentation in t_cose_crypto.h
 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
enum t_cose_err_t t_cose_crypto_el3_token_sign_restart(
	bool started, int32_t cose_algorithm_id, struct t_cose_key signing_key,
	void *crypto_context, struct q_useful_buf_c hash_to_sign,
	struct q_useful_buf signature_buffer, struct q_useful_buf_c *signature)
{
	enum t_cose_err_t return_value;
	struct t_cose_el3_token_sign_ctx *el3_crypto_context;
	psa_algorithm_t psa_alg_id;

	(void)signing_key;

	assert(cb_initialized);

	psa_alg_id = cose_alg_id_to_psa_alg_id(cose_algorithm_id);
	if (!PSA_ALG_IS_ECDSA(psa_alg_id)) {
		return_value = T_COSE_ERR_UNSUPPORTED_SIGNING_ALG;
		goto done;
	}

	if (crypto_context == NULL) {
		return_value = T_COSE_ERR_FAIL;
		goto done;
	}

	el3_crypto_context = (struct t_cose_el3_token_sign_ctx *)crypto_context;

	/*
	 * Since the response corresponding to this REC can be updated by
	 * another REC we need to protect the below from concurrent access.
	 */
	spinlock_acquire(&el3_crypto_context->lock);
	if (!started) {
		t_cose_crypto_init_el3_ctx_crypto(el3_crypto_context,
						  psa_alg_id,
						  hash_to_sign,
						  signature_buffer);
	}

	if (!el3_crypto_context->state.is_req_queued) {
		int ret;
		/*
		 * The callback is called with the lock held for the context
		 * and imposes lock ordering constraints on the call back to
		 * ensure there are no dead locks.
		 * lock ordering: el3_crypto_context->lock -> any lock held
		 * by the callback.
		 */
		ret = t_cose_crypto_el3_enqueue(el3_crypto_context,
			&el3_crypto_context->state.req_ticket);
		if (ret == 0) {
			el3_crypto_context->state.is_req_queued = true;
		} else if (ret != -EAGAIN) {
			return_value = T_COSE_ERR_FAIL;
			ERROR("%s:%d: EL3 Token Sign queuing failed.\n",
				__func__, __LINE__);
			goto release;
		}
	}

	/*
	 * Responses for this request are pulled outside the current function
	 */
	if (el3_crypto_context->state.is_el3_err) {
		return_value = T_COSE_ERR_FAIL;
		ERROR("%s:%d: EL3 Token Sign failed when pulling response\n",
		      __func__, __LINE__);
		goto release;
	}

	return_value = T_COSE_ERR_SIG_IN_PROGRESS;

	if (el3_crypto_context->state.is_sig_valid) {
		assert(el3_crypto_context->state.is_req_queued == true);
		assert(el3_crypto_context->state.sig_len <= signature_buffer.len);
		signature->ptr = signature_buffer.ptr;
		signature->len = el3_crypto_context->state.sig_len;
		return_value = T_COSE_SUCCESS;
	}

release:
	spinlock_release(&el3_crypto_context->lock);
done:
	return return_value;
}

/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
enum t_cose_err_t t_cose_crypto_el3_token_sign(int32_t cose_algorithm_id,
					 struct t_cose_key signing_key,
					 void *crypto_context,
					 struct q_useful_buf_c hash_to_sign,
					 struct q_useful_buf signature_buffer,
					 struct q_useful_buf_c *signature)
{
	(void)cose_algorithm_id;
	(void)signing_key;
	(void)crypto_context;
	(void)hash_to_sign;
	(void)signature_buffer;
	(void)signature;

	return T_COSE_ERR_UNSUPPORTED_SIGNING_ALG;
}

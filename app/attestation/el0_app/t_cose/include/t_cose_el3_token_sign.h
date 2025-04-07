/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef T_COSE_EL3_TOKEN_SIGN_H
#define T_COSE_EL3_TOKEN_SIGN_H

#include <spinlock.h>
#include <t_cose_psa_crypto.h>

struct t_cose_el3_token_sign_ctx {

	/*
	 * Some of the operations in the crypto adaption layer might use the
	 * crypto context. Make sure that casting this context to
	 * `struct t_cose_psa_crypto_context` by them is safe.
	 */
	struct t_cose_psa_crypto_context psa_crypto_context;

	spinlock_t lock;
	struct {
		/* cppcheck-suppress misra-c2012-6.1 */
		bool is_req_queued : 1U;
		/* cppcheck-suppress misra-c2012-6.1 */
		bool is_sig_valid : 1U;
		/* cppcheck-suppress misra-c2012-6.1 */
		bool is_el3_err : 1U;
		psa_algorithm_t sign_alg_id;
		uintptr_t cookie;
		uint64_t req_ticket;
		size_t sig_len;
		void *sig_buffer;
		size_t hash_len;
		const void *hash_buffer;
	} state;
};
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct t_cose_el3_token_sign_ctx, psa_crypto_context)) == 0U);

/*
 * Callback function for the t_cose lib to be able to enqueue a signing request.
 * The function is expected to return true if the request was successfully queued
 * and false otherwise.
 * The t_cose adaptation will call this function with the lock held for el3_ctx. Since
 * the lock is held, it imposes lock ordering constraints on the call back.
 *
 * The callback returns 0 on success, -EAGAIN to try queuing again or other negative
 * error codes for any other error.
 */
typedef int (*t_cose_crypto_el3_enqueue_t)(struct t_cose_el3_token_sign_ctx *el3_ctx,
						uint64_t *ticket);

/*
 * Initialize enqueue callback with the library. This is expected to be called
 * once during boot.
 */
void t_cose_crypto_el3_enqueue_cb_init(t_cose_crypto_el3_enqueue_t enqueue);

/*
 * Initialize the el3 token signing context and associate with the
 * granule address of the REC it is associated with. The library user
 * must call this function when the context is first used or being
 * reused for a new signing operation.
 */
void t_cose_crypto_el3_ctx_init(struct t_cose_el3_token_sign_ctx *el3_ctx,
				uintptr_t cookie);

#endif /* T_COSE_EL3_TOKEN_SIGN_H */

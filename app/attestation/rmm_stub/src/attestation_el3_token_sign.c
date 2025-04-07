/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <app_common.h>
#include <assert.h>
#include <atomics.h>
#include <attest_app.h>
#include <cpuid.h>
#include <debug.h>
#include <errno.h>
#include <rmm_el3_ifc.h>
#include <spinlock.h>
#include <stdbool.h>
#include <string.h>

static uint64_t el3_token_sign_ticket = 1;

static struct el3_token_sign_response token_sign_response[MAX_CPUS] = { 0 };

/*
 * Callback is called with lock held for the context and imposes lock ordering.
 * Since this function holds the lock for the shared buffer, the lock ordering
 * ctx->lock -> rmm_el3_ifc_get_shared_buf_locked() is expected to be followed.
 * attest_el3_token_write_response_to_ctx() is called with the lock held for a
 * given REC granule and imposes lock ordering of granule lock -> ctx->lock.
 */
int el3_token_sign_queue_try_enqueue(struct service_el3_token_sign_request *request)
{
	int ret = 0;
	struct el3_token_sign_request *req;

	if ((request == NULL) ||
	    (request->hash_buf_len > sizeof(req->hash_buf))) {
		return -EINVAL;
	}

	req = (struct el3_token_sign_request *)rmm_el3_ifc_get_shared_buf_locked();
	/* TODO: For now only ECC_SECP384 is supported */
	req->sign_alg_id = ATTEST_KEY_CURVE_ECC_SECP384R1;
	req->cookie = request->cookie;
	/* TODO: For now only SHA384 is supported */
	req->hash_alg_id = EL3_TOKEN_SIGN_HASH_ALG_SHA384;
	(void)memcpy((void *)(req->hash_buf), request->hash_buf,
		request->hash_buf_len);

	/*
	 * Overflow of the 64 bit number will occur after ~580 years at
	 * 1 ns resolution. Even if it does overflow, the ticket will be
	 * 0 and is still valid. Overflow is not expected to be a problem.
	 */
	req->req_ticket = atomic_load_add_64(&el3_token_sign_ticket, 1);
	request->ticket = req->req_ticket;

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

int attest_el3_token_write_response_to_ctx(struct app_data_cfg *app_data, uintptr_t cookie)
{
	struct el3_token_sign_response *el3_resp = &token_sign_response[my_cpuid()];

	if ((uint64_t)cookie != el3_resp->cookie) {
		VERBOSE("Response for REC granule %lx not found\n",
			 el3_resp->cookie);
		return -EINVAL;
	}

	return attest_app_el3_token_write_response_to_ctx(app_data,
						  el3_resp->req_ticket,
						  el3_resp->sig_len,
						  el3_resp->signature_buf);
}

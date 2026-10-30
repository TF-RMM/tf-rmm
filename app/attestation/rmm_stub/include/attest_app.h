/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ATTEST_APP_H
#define ATTEST_APP_H

#include <app.h>
#include <attest_defs.h>
#include <sizes.h>
#include <smc-rmi.h>
#include <stddef.h>


void attest_do_hash(unsigned int algorithm,
		    void *data,
		    size_t size,
		    unsigned char *out);
void attest_do_extend(struct app_data_cfg *app_data,
		      enum hash_algo algorithm,
		      void *current_measurement,
		      void *extend_measurement,
		      size_t extend_measurement_size,
		      unsigned char *out,
		      size_t out_size);

/*
 * Initialize shared attestation state once per image on the primary CPU,
 * after global data setup and before any REC runs. Retrieves the RAK and,
 * when ATTEST_EL3_TOKEN_SIGN is enabled, establishes the EL3 response ticket
 * boundary. Return zero on success or an initialization error.
 */
int attest_app_global_init(void);

/* Init an app instance for this CPU */
void attest_app_init_per_cpu_instance(void);

/*
 * Delete the thread associated with an attestation app
 * ONLY A WRAPPER - Ensure correct app_data is specified
 */
int attest_app_delete(struct app_data_cfg *app_data);

enum attest_token_err_t attest_realm_token_sign(
			struct app_data_cfg *app_data,
			size_t *realm_token_len);
enum attest_token_err_t attest_cca_token_create(
				struct app_data_cfg *app_data,
				size_t *attest_token_len);
enum attest_token_err_t attest_token_sign_ctx_init(
				struct app_data_cfg *app_data,
				uintptr_t cookie);
enum attest_token_err_t  attest_realm_token_create(struct app_data_cfg *app_data,
			     enum hash_algo algorithm,
			     unsigned char measurements[][MAX_MEASUREMENT_SIZE],
			     bool is_pvt_mecid,
			     const void *realm_instance_id_buf,
			     const void *rpv_buf,
			     const void *challenge_buf);

/* This API is private for this rmm-stub. */
int attest_app_el3_token_write_response_to_ctx(struct app_data_cfg *app_data,
					       uint64_t req_ticket,
					       size_t signature_buf_len,
					       uint8_t signature_buf[]);

/*
 * Reserve the EL3 signing ticket boundary for this image. Called once on the
 * primary CPU after global data setup, before any REC enqueues or receives
 * a response. This API is private to the RMM stub and is available only when
 * ATTEST_EL3_TOKEN_SIGN is enabled.
 */
void attest_el3_token_sign_init(void);

/*
 * Write the per-CPU EL3 response to the context if the cookie matches and
 * the request was issued by this image. Old-image responses are discarded
 * before entering the app, whose retained heap may have an obsolete layout.
 * The app checks that a current-image response matches its active request.
 * The caller must pin the REC with a reference or its granule lock.
 * Return zero on delivery or discard, -EINVAL for a cookie mismatch, or the
 * app's error. The caller must treat nonzero returns as fatal errors.
 */
int attest_el3_token_write_response_to_ctx(struct app_data_cfg *app_data, uintptr_t cookie);

/*
 * Pull the response from EL3 into the per cpu response buffer. The function
 * returns the cookie associated with the response. The response could correspond
 * to current REC or another REC which had requested the EL3 service.
 *
 * Arguments:
 * cookie		- Pointer to storage of cookie to return the value from
 *			  response.
 *
 * Return code:
 *	0		- Success
 *	-EAGAIN		- Response not ready. Call this API again.
 *	-ENOTSUP	- Other error including EL3_TOKEN_SIGN not supported in
 *			  EL3 firmware.
 */
int attest_el3_token_sign_pull_response_from_el3(uintptr_t *cookie);

/*
 * ONLY FOR TESTING PURPOSES.
 * Reset all per-cpu attest app instance state. Must be called after
 * app_processes_cleanup() to prevent stale FDs/thread IDs being used.
 */
void attest_reset_app_state(void);

#endif /* ATTEST_APP_H */

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

/* Do the global initialisation for the attestation app
 * This function gets the RAK from EL3, and stores it in the app keystore.
 */
int attest_app_global_init(void);

/* Init an app instance for this CPU */
void attest_app_init_per_cpu_instance(void);

/* Iniialise a new app instance in the app_data object */
int attest_app_init(struct app_data_cfg *app_data,
	uintptr_t granule_pas[],
	size_t granule_pa_count,
	void *granule_va_start);
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
			     const void *rpv_buf,
			     const void *challenge_buf);

/* This API is private for this rmm-stub. */
int attest_app_el3_token_write_response_to_ctx(struct app_data_cfg *app_data,
					       uint64_t req_ticket,
					       size_t signature_buf_len,
					       uint8_t signature_buf[]);

/*
 * Write the response from EL3 to the context. The response is written only if the context
 * is valid and the response is for the right request. If the function returns an error
 * the caller must treat it as a fatal error. The cookie is checked against the per cpu
 * response buffer to ensure that the response is for the right request.
 * The caller must ensure that the REC granule lock is held so that it cannot be deleted
 * while the response is being written.
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

#endif /* ATTEST_APP_H */

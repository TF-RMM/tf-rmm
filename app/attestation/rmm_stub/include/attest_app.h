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
	size_t granule_pa_count);
enum attest_token_err_t attest_realm_token_sign(
			struct app_data_cfg *app_data,
			size_t *realm_token_len);
enum attest_token_err_t attest_cca_token_create(
				struct app_data_cfg *app_data,
				void *attest_token_buf,
				size_t attest_token_buf_size,
				size_t *attest_token_len);
enum attest_token_err_t attest_token_sign_ctx_init(
				struct app_data_cfg *app_data,
				uintptr_t cookie);
enum attest_token_err_t  attest_realm_token_create(struct app_data_cfg *app_data,
			     enum hash_algo algorithm,
			     unsigned char measurements[][MAX_MEASUREMENT_SIZE],
			     const void *rpv_buf,
			     const void *challenge_buf);
#endif /* ATTEST_APP_H */

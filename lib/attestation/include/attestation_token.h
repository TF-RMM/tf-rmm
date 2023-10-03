/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright Laurence Lundblade.
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 * This file is derived from:
 *    trusted-firmware-m/secure_fw/partitions/initial_attestation/attest_token.h
 */

#ifndef ATTESTATION_TOKEN_H
#define ATTESTATION_TOKEN_H

#include <measurement.h>
#include <qcbor/qcbor.h>
#include <t_cose/q_useful_buf.h>
#include <t_cose/t_cose_sign_sign.h>
#include <t_cose/t_cose_signature_sign_restart.h>
#include <t_cose_psa_crypto.h>

#define ATTEST_TOKEN_BUFFER_SIZE		GRANULE_SIZE

enum attest_token_err_t {
	/* Success */
	ATTEST_TOKEN_ERR_SUCCESS = 0,
	/* The buffer passed in to receive the output is too small. */
	ATTEST_TOKEN_ERR_TOO_SMALL,
	/*
	 * Something went wrong formatting the CBOR, most likely the
	 * payload has maps or arrays that are not closed.
	 */
	ATTEST_TOKEN_ERR_CBOR_FORMATTING,
	/* Signing key is not found or of wrong type. */
	ATTEST_TOKEN_ERR_SIGNING_KEY,
	ATTEST_TOKEN_ERR_COSE_ERROR,
	/* Signing is in progress, function should be called with the same
	 * parameters again.
	 */
	ATTEST_TOKEN_ERR_COSE_SIGN_IN_PROGRESS
};

/* The state of the realm token generation */
enum attest_token_gen_state_t {
	ATTEST_SIGN_NOT_STARTED,
	ATTEST_SIGN_IN_PROGRESS,
	ATTEST_SIGN_TOKEN_WRITE_IN_PROGRESS
};

/*
 * The context for creating an attestation token. The caller of
 * attest_token_encode must create one of these and pass it to the functions
 * here. It is small enough that it can go on the stack. It is most of
 * the memory needed to create a token except the output buffer and
 * any memory requirements for the cryptographic operations.
 *
 * The structure is opaque for the caller.
 *
 * This is roughly 148 + 8 + 32 = 188 bytes
 */

struct attest_token_encode_ctx {
	/* Private data structure */
	QCBOREncodeContext                            cbor_enc_ctx;
	uint32_t                                      opt_flags;
	int32_t                                       key_select;
	struct q_useful_buf_c                         signed_payload;
	struct t_cose_sign_sign_ctx                   sign_ctx;
	struct t_cose_signature_sign_restart          restartable_signer_ctx;
	struct t_cose_psa_crypto_context              crypto_ctx;
};

#define ATTEST_CHALLENGE_SIZE			(64)

/*
 * The context for signing an attestation token. Each REC contains one context
 * that is passed to the attestation library during attestation token creation
 * to keep track of the signing state.
 */
struct token_sign_cntxt {
	/*
	 * 'state' is used to implement a state machine
	 * to track the current state of signing.
	 */
	enum attest_token_gen_state_t state;
	struct attest_token_encode_ctx ctx;

	/* Number of CCA token bytes left to copy to the Realm */
	size_t cca_token_len;

	/* Number of CCA token bytes copied to the Realm */
	size_t copied_len;

	unsigned char challenge[ATTEST_CHALLENGE_SIZE];
};

/*
 * Sign the realm token and complete the CBOR encoding.
 * This function returns ATTEST_TOKEN_ERR_COSE_SIGN_IN_PROGRESS
 * if signing is not complete and this function needs to be
 * invoked again. ATTEST_TOKEN_ERR_SUCCESS is returned if
 * signing is complete and `completed_token` is valid.
 * Else returns one of the attest_token_err_t errors on
 * any other error.
 *
 * me				Token Creation Context.
 * completed_token_len		Length of the completed token.
 *
 * This completes the token after the payload has been added. When
 * this is called the signing algorithm is run and the final
 * formatting of the token is completed.
 */
enum attest_token_err_t
attest_realm_token_sign(struct attest_token_encode_ctx *me,
			size_t *completed_token_len);

/*
 * Combine realm token and platform token to top-level cca token
 *
 * attest_token_buf		Pointer to the buffer where the token will be
 *				written.
 * attest_token_buf_size	Size of the buffer where the token will be
 *				written.
 * realm_token_buf	Pointer to the realm token.
 * realm_token_len	Length of the realm token.
 *
 * Return 0 in case of error, the length of the cca token otherwise.
 */
size_t attest_cca_token_create(void *attest_token_buf,
				size_t attest_token_buf_size,
				const void *realm_token_buf,
				size_t realm_token_len);

/*
 * Assemble the Realm token in the buffer provided in realm_token_buf,
 * except the signature.
 *
 * Arguments:
 * Algorithm		- Algorithm used during measurement.
 * Measurement		- Array of buffers containing all the measurements.
 * num_measurements	- Number of measurements to add to the token.
 * rpv_buf              - Pointer to the Realm Personalization value
 * rpv_len              - Length of the Realm Personalization value
 * ctx			- Token sign context, used for signing.
 * realm_token_buf	- Buffer where to assemble the attestation token.
 * realm_token_buf_size - size of the buffer where to assemble the attestation
 *                        token.
 *
 * Returns ATTEST_TOKEN_ERR_SUCCESS (0) on success or a negative error code
 * otherwise.
 */
int attest_realm_token_create(enum hash_algo algorithm,
			     unsigned char measurements[][MAX_MEASUREMENT_SIZE],
			     unsigned int num_measurements,
			     const void *rpv_buf,
			     size_t rpv_len,
			     struct token_sign_cntxt *ctx,
			     void *realm_token_buf,
			     size_t realm_token_buf_size);

#endif /* ATTESTATION_TOKEN_H */

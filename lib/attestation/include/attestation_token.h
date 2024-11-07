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
#ifndef CBMC
#include <qcbor/qcbor.h>
#endif /* CBMC */
#include <stddef.h>
#include <stdint.h>
#ifndef CBMC
#include <t_cose/q_useful_buf.h>
#include <t_cose/t_cose_sign_sign.h>
#include <t_cose/t_cose_signature_sign_restart.h>
#include <t_cose_el3_token_sign.h>
#include <t_cose_psa_crypto.h>
#endif /* CBMC */

/* The state of the CCA token generation */
enum attest_token_gen_state_t {
	ATTEST_TOKEN_NOT_STARTED,	/* Initial phase */
	ATTEST_TOKEN_INIT,		/* Initialized */
	ATTEST_TOKEN_SIGN,		/* Realm token sign */
	ATTEST_TOKEN_CREATE,		/* CCA Token create */
};

#ifndef CBMC

#define ATTEST_TOKEN_BUFFER_SIZE		GRANULE_SIZE

enum attest_token_err_t {
	/* Success */
	ATTEST_TOKEN_ERR_SUCCESS = 0,
	/* The Attest token context state is incorrect */
	ATTEST_TOKEN_ERR_INVALID_STATE,
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
	/*
	 * Signing is in progress, function should be called with the same
	 * parameters again.
	 */
	ATTEST_TOKEN_ERR_COSE_SIGN_IN_PROGRESS,
	/*
	 * Error code to return when CCA token creation fails.
	 */
	ATTEST_TOKEN_ERR_CCA_TOKEN_CREATE
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
#if ATTEST_EL3_TOKEN_SIGN
	struct t_cose_el3_token_sign_ctx              crypto_ctx;
#else
	struct t_cose_psa_crypto_context              crypto_ctx;
#endif
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
};

#else /* CBMC */

#define ATTEST_TOKEN_BUFFER_SIZE		GRANULE_SIZE

enum attest_token_err_t {
	/* Success */
	ATTEST_TOKEN_ERR_SUCCESS = 0,
	/*
	 * Signing is in progress, function should be called with the same
	 * parameters again.
	 */
	ATTEST_TOKEN_ERR_COSE_SIGN_IN_PROGRESS
};

struct attest_token_encode_ctx {
	uint32_t unused;
};

struct token_sign_cntxt {
	enum attest_token_gen_state_t state;
};

#define ATTEST_CHALLENGE_SIZE			(1)

#endif /* CBMC */

/*
 * Sign the realm token and complete the CBOR encoding.
 * This function returns ATTEST_TOKEN_ERR_COSE_SIGN_IN_PROGRESS
 * if signing is not complete and this function needs to be
 * invoked again. ATTEST_TOKEN_ERR_SUCCESS is returned if
 * signing is complete and `completed_token` is valid.
 * Else returns one of the attest_token_err_t errors on
 * any other error.
 *
 * me				Token Sign Context.
 * completed_token_len		Length of the completed token.
 *
 * This completes the token after the payload has been added. When
 * this is called the signing algorithm is run and the final
 * formatting of the token is completed.
 */
enum attest_token_err_t
attest_realm_token_sign(struct token_sign_cntxt *me,
			size_t *completed_token_len);

/*
 * Combine realm token and platform token to top-level cca token
 *
 * me				Token Sign Context.
 * attest_token_buf		Pointer to the buffer where the token will be
 *				written.
 * attest_token_buf_size	Size of the buffer where the token will be
 *				written.
 * realm_token_buf		Pointer to the realm token.
 * realm_token_len		Length of the realm token.
 * cca_token_len		Returns the length of top-level CCA token
 *
 * Returns ATTEST_TOKEN_ERR_SUCCESS (0) if CCA top-level token is
 * created. Otherwise, returns the proper error value.
 */
enum attest_token_err_t
attest_cca_token_create(struct token_sign_cntxt *me,
				void *attest_token_buf,
				size_t attest_token_buf_size,
				const void *realm_token_buf,
				size_t realm_token_len,
				size_t *cca_token_len);

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
			     const void *challenge_buf,
			     size_t challenge_len,
			     struct token_sign_cntxt *ctx,
			     void *realm_token_buf,
			     size_t realm_token_buf_size);

/*
 * Initialize the token sign context and also the heap buffer used for the crypto.
 * It is assumed that the heap alloc context has already been assigned to this
 * CPU. If the token sign context has already been initialized, this API will
 * not initialize again as an optimization.
 *
 * Arguments:
 * token_ctx		- Token sign context.
 * heap_buf		- Buffer to use as heap.
 * heap_buf_len		- Size of the buffer to use as heap.
 * cookie		- Unique cookie to associate with the context (ex rec granule PA)
 *
 * Return code:
 *	ATTEST_TOKEN_ERR_SUCCESS (0)	- Success.
 *	ATTEST_TOKEN_ERR_INVALID_STATE	- Failed possibly due to invalid state.
 */
enum attest_token_err_t attest_token_ctx_init(struct token_sign_cntxt *token_ctx,
			   unsigned char *heap_buf,
			   unsigned int heap_buf_len,
			   uintptr_t cookie);

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
 * 	0		- Success
 * 	-EAGAIN		- Response not ready. Call this API again.
 * 	-ENOTSUP	- Other error including EL3_TOKEN_SIGN not supported in
 *			  EL3 firmware.
 */
int attest_el3_token_sign_pull_response_from_el3(uintptr_t *cookie);

/*
 * Write the response from EL3 to the context. The response is written only if the context
 * is valid and the response is for the right request. If the function returns an error
 * the caller must treat it as a fatal error. The cookie is checked against the per cpu
 * response buffer to ensure that the response is for the right request.
 * The caller must ensure that the REC granule lock is held so that it cannot be deleted
 * while the response is being written.
 *
 * Arguments:
 * ctx			- Pointer to token_sign_cntxt
 * cookie		- Pointer to storage of cookie to return the value from
 *			  response.
 *
 * Returns 0 on success or a negative error code otherwise.
 */
int attest_el3_token_write_response_to_ctx(struct token_sign_cntxt *sign_ctx, uintptr_t cookie);

#endif /* ATTESTATION_TOKEN_H */

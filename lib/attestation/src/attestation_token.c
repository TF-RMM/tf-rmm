/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright Laurence Lundblade.
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 * This file is derived from:
 *    trusted-firmware-m/secure_fw/partitions/initial_attestation/attest_token_encode.c
 */

#include <assert.h>
#include <attestation.h>
#include <attestation_defs_priv.h>
#include <attestation_priv.h>
#include <attestation_token.h>
#include <debug.h>
#include <measurement.h>
#include <qcbor/qcbor.h>
#include <simd.h>
#include <t_cose/q_useful_buf.h>
#include <t_cose/t_cose_common.h>
#include <t_cose/t_cose_sign1_sign.h>
#include <utils_def.h>

/*
 * According to IANA hash algorithm registry:
 *   - https://www.iana.org/assignments/hash-function-text-names/hash-function-text-names.xml
 */
static void attest_get_hash_algo_text(enum hash_algo algorithm,
				      struct q_useful_buf_c *algo_text)
{
	const char *sha256 = "sha-256";
	const char *sha512 = "sha-512";

	switch (algorithm) {
	case HASH_SHA_256:
		*algo_text = UsefulBuf_FromSZ(sha256);
		break;
	case HASH_SHA_512:
		*algo_text = UsefulBuf_FromSZ(sha512);
		break;
	default:
		assert(false);
	}
}

/*
 * Outline of token creation. Much of this occurs inside
 * t_cose_sign1_encode_parameters() and t_cose_sign1_encode_signature().
 *
 * - Create encoder context
 * - Open the CBOR array that hold the COSE_Sign1
 * - Write COSE Headers
 *   - Protected Header
 *      - Algorithm ID
 *   - Unprotected Headers
 *     - Key ID
 * - Open payload bstr
 *   - Write payload data, maybe lots of it
 *   - Get bstr that is the encoded payload
 * - Compute signature
 *   - Create a separate encoder context for Sig_structure
 *     - Encode CBOR context identifier
 *     - Encode protected headers
 *     - Encode two empty bstr
 *     - Add one more empty bstr that is a "fake payload"
 *     - Close off Sig_structure
 *   - Hash all but "fake payload" of Sig_structure
 *   - Get payload bstr ptr and length
 *   - Continue hash of the real encoded payload
 *   - Run ECDSA
 * - Write signature into the CBOR output
 * - Close CBOR array holding the COSE_Sign1
 */
static enum attest_token_err_t
attest_token_encode_start(struct attest_token_encode_ctx *me,
			  uint32_t opt_flags,
			  int32_t key_select,
			  int32_t cose_alg_id,
			  const struct q_useful_buf *out_buf)
{
	enum t_cose_err_t cose_res;
	struct t_cose_key attest_key;
	psa_key_handle_t key_handle;

	assert(me != NULL);

	/* Remember some of the configuration values */
	me->opt_flags  = opt_flags;
	me->key_select = key_select;

	t_cose_signature_sign_restart_init(&me->restartable_signer_ctx, cose_alg_id);
	t_cose_signature_sign_restart_set_crypto_context(&me->restartable_signer_ctx, &(me->crypto_ctx));
	t_cose_sign_sign_init(&me->sign_ctx, T_COSE_OPT_MESSAGE_TYPE_SIGN1);
	t_cose_sign_add_signer(&me->sign_ctx, t_cose_signature_sign_from_restart(&me->restartable_signer_ctx));


	/*
	 * Get the reference to `mbedtls_ecp_keypair` and set it to t_cose.
	 */
	if (attest_get_realm_signing_key(&key_handle) != 0) {
		return ATTEST_TOKEN_ERR_SIGNING_KEY;
	}

	attest_key.key.handle = key_handle;

	t_cose_signature_sign_restart_set_signing_key(&me->restartable_signer_ctx, attest_key);

	/* Spin up the CBOR encoder */
	QCBOREncode_Init(&(me->cbor_enc_ctx), *out_buf);

	/*
	 * This will cause the cose headers to be encoded and written into
	 * out_buf using me->cbor_enc_ctx
	 */
	cose_res = t_cose_sign_encode_start(&me->sign_ctx, &me->cbor_enc_ctx);

	if (cose_res != T_COSE_SUCCESS) {
		return ATTEST_TOKEN_ERR_COSE_ERROR;
	}

	return ATTEST_TOKEN_ERR_SUCCESS;
}

enum attest_token_err_t
attest_realm_token_sign(struct attest_token_encode_ctx *me,
			size_t *completed_token_len)
{
	/* The completed and signed encoded cose_sign1 */
	struct q_useful_buf_c completed_token_ub;
	enum attest_token_err_t attest_res = ATTEST_TOKEN_ERR_SUCCESS;
	QCBORError qcbor_res;
	enum t_cose_err_t cose_res;

	assert(me != NULL);
	assert(completed_token_len != NULL);

	/* Finish up the COSE_Sign1. This is where the signing happens */
	SIMD_FPU_ALLOW(
		cose_res = t_cose_sign_encode_finish(&me->sign_ctx,
						     NULL_Q_USEFUL_BUF_C,
						     me->signed_payload,
						     &me->cbor_enc_ctx));

	if (cose_res == T_COSE_ERR_SIG_IN_PROGRESS) {
		/* Token signing has not yet finished */
		return ATTEST_TOKEN_ERR_COSE_SIGN_IN_PROGRESS;
	}

	if (cose_res != T_COSE_SUCCESS) {
		/* Main errors are invoking the hash or signature */
		return ATTEST_TOKEN_ERR_COSE_ERROR;
	}

	/*
	 * Finally close off the CBOR formatting and get the pointer and length
	 * of the resulting COSE_Sign1
	 */
	qcbor_res = QCBOREncode_Finish(&(me->cbor_enc_ctx),
				       &completed_token_ub);

	switch (qcbor_res) {
	case QCBOR_ERR_BUFFER_TOO_SMALL:
		attest_res = ATTEST_TOKEN_ERR_TOO_SMALL;
		break;
	case QCBOR_SUCCESS:
		/* coverity[uninit_use:SUPPRESS] */
		*completed_token_len = completed_token_ub.len;
		break;
	default:
		/* likely from array not closed, too many closes ... */
		attest_res = ATTEST_TOKEN_ERR_CBOR_FORMATTING;
	}

	return attest_res;
}

size_t attest_cca_token_create(void *attest_token_buf,
			       size_t attest_token_buf_size,
			       const void *realm_token_buf,
			       size_t realm_token_len)
{
	struct q_useful_buf_c   completed_token;
	QCBOREncodeContext      cbor_enc_ctx;
	QCBORError              qcbor_res;
	struct q_useful_buf_c   platform_token;
	struct q_useful_buf     attest_token_ub = {attest_token_buf, attest_token_buf_size};
	struct q_useful_buf_c   realm_token_ub = {realm_token_buf, realm_token_len};

	__unused int            ret;

	/* Get the platform token */
	ret = attest_get_platform_token(&platform_token.ptr,
					&platform_token.len);
	assert(ret == 0);

	QCBOREncode_Init(&cbor_enc_ctx, attest_token_ub);

	QCBOREncode_AddTag(&cbor_enc_ctx, TAG_CCA_TOKEN);

	QCBOREncode_OpenMap(&cbor_enc_ctx);

	QCBOREncode_AddBytesToMapN(&cbor_enc_ctx,
				   CCA_PLAT_TOKEN,
				   platform_token);

	QCBOREncode_AddBytesToMapN(&cbor_enc_ctx,
				   CCA_REALM_DELEGATED_TOKEN,
				   realm_token_ub);
	QCBOREncode_CloseMap(&cbor_enc_ctx);

	qcbor_res = QCBOREncode_Finish(&cbor_enc_ctx, &completed_token);

	if (qcbor_res == QCBOR_ERR_BUFFER_TOO_SMALL) {
		ERROR("CCA output token buffer too small\n");
		return 0;
	} else if (qcbor_res != QCBOR_SUCCESS) {
		/* likely from array not closed, too many closes, ... */
		assert(false);
	} else {
		/* coverity[uninit_use:SUPPRESS] */
		return completed_token.len;
	}
	return 0;
}

/*
 * Assemble the Realm Attestation Token in the buffer provided in
 * realm_token_buf, except the signature.
 *
 * As per section A7.2.3.1 of RMM specfication, Realm Attestation token is
 * composed of:
 *	- Realm Challenge
 *	- Realm Personalization Value
 *	- Realm Hash Algorithm Id
 *	- Realm Public Key
 *	- Realm Public Key Hash Algorithm Id
 *	- Realm Initial Measurement
 *	- Realm Extensible Measurements
 */
int attest_realm_token_create(enum hash_algo algorithm,
			     unsigned char measurements[][MAX_MEASUREMENT_SIZE],
			     unsigned int num_measurements,
			     const void *rpv_buf,
			     size_t rpv_len,
			     struct token_sign_cntxt *ctx,
			     void *realm_token_buf,
			     size_t realm_token_buf_size)
{
	struct q_useful_buf_c buf;
	size_t measurement_size;
	enum attest_token_err_t token_ret;
	struct q_useful_buf realm_token_ub = {realm_token_buf, realm_token_buf_size};
	struct q_useful_buf_c rpv_ub = {rpv_buf, rpv_len};
	int ret;

	/* Can only be called in the init state */
	assert(ctx->state == ATTEST_SIGN_NOT_STARTED);

	assert(num_measurements == MEASUREMENT_SLOT_NR);

	/*
	 * Get started creating the token. This sets up the CBOR and COSE
	 * contexts which causes the COSE headers to be constructed.
	 */
	token_ret = attest_token_encode_start(&(ctx->ctx),
					      0,     /* option_flags */
					      0,     /* key_select */
					      T_COSE_ALGORITHM_ES384,
					      &realm_token_ub);
	if (token_ret != ATTEST_TOKEN_ERR_SUCCESS) {
		return (int)token_ret;
	}

	QCBOREncode_BstrWrap(&(ctx->ctx.cbor_enc_ctx));
	QCBOREncode_OpenMap(&(ctx->ctx.cbor_enc_ctx));

	/* Add challenge value, which is the only input from the caller. */
	buf.ptr = ctx->challenge;
	buf.len = ATTEST_CHALLENGE_SIZE;
	QCBOREncode_AddBytesToMapN(&(ctx->ctx.cbor_enc_ctx),
				   CCA_REALM_CHALLENGE,
				   buf);

	QCBOREncode_AddBytesToMapN(&(ctx->ctx.cbor_enc_ctx),
				   CCA_REALM_PERSONALIZATION_VALUE,
				   rpv_ub);

	ret = attest_get_realm_public_key(&buf);
	if (ret != 0) {
		return ret;
	}

	QCBOREncode_AddBytesToMapN(&(ctx->ctx.cbor_enc_ctx),
				   CCA_REALM_PUB_KEY,
				   buf);

	attest_get_hash_algo_text(algorithm, &buf);
	QCBOREncode_AddTextToMapN(&(ctx->ctx.cbor_enc_ctx),
				  CCA_REALM_HASH_ALGM_ID,
				  buf);

	attest_get_hash_algo_text(attest_get_realm_public_key_hash_algo_id(),
				  &buf);
	QCBOREncode_AddTextToMapN(&(ctx->ctx.cbor_enc_ctx),
				  CCA_REALM_PUB_KEY_HASH_ALGO_ID,
				  buf);

	measurement_size = measurement_get_size(algorithm);
	assert(measurement_size <= MAX_MEASUREMENT_SIZE);

	/* RIM: 0, REM: 1..4 */
	buf.ptr = &measurements[RIM_MEASUREMENT_SLOT];
	buf.len = measurement_size;
	QCBOREncode_AddBytesToMapN(&(ctx->ctx.cbor_enc_ctx),
				   CCA_REALM_INITIAL_MEASUREMENT,
				   buf);

	QCBOREncode_OpenArrayInMapN(&(ctx->ctx.cbor_enc_ctx),
				    CCA_REALM_EXTENSIBLE_MEASUREMENTS);

	for (unsigned int i = 1U; i < num_measurements; ++i) {
		buf.ptr = &measurements[i];
		buf.len = measurement_size;
		QCBOREncode_AddBytes(&(ctx->ctx.cbor_enc_ctx), buf);
	}

	QCBOREncode_CloseArray(&(ctx->ctx.cbor_enc_ctx));
	QCBOREncode_CloseMap(&(ctx->ctx.cbor_enc_ctx));
	QCBOREncode_CloseBstrWrap2(&(ctx->ctx.cbor_enc_ctx), false,
				   &(ctx->ctx.signed_payload));

	return ATTEST_TOKEN_ERR_SUCCESS;
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_common.h>
#include <assert.h>
#include <attest_defs.h>
#include <attestation_priv.h>
#include <debug.h>
#include <el0_app_helpers.h>
#include <errno.h>
#include <psa/crypto.h>
#include <sizes.h>
#include <t_cose/q_useful_buf.h>
#include <t_cose/t_cose_common.h>
#include <t_cose/t_cose_sign1_sign.h>

/*
 * COSE_Key object:       RFC 8152, Section 7
 * Key Object Parameters: RFC 8152, Section 13
 *
 * The t_cose lib encodes the EC2 public key as:
 *
 *    COSE_Key = {
 *        1 => int,  ; kty
 *       -1 => int,  ; crv
 *       -2 => bstr, ; x-coordinate
 *       -3 => bstr, ; y-coordinate
 *    }
 */
/* coverity[misra_c_2012_rule_12_1_violation:SUPPRESS] */
#define MAX_REALM_PUBLIC_KEY_SIZE	(PSA_KEY_EXPORT_ECC_PUBLIC_KEY_MAX_SIZE(384U) + \
					 32U) /* kty and crv + encoding */

/*
 * The platform token which will be needed during attestation.
 */
static unsigned char rmm_platform_token_buf[ATTEST_PLAT_TOKEN_SIZE];
static struct q_useful_buf rmm_platform_token;

/*
 * The public key is kept loaded as it is both not required to be secret (and
 * hence can be kept in attestation memory) and immutable.
 */
/* coverity[misra_c_2012_rule_12_1_violation:SUPPRESS] */
static uint8_t realm_attest_public_key[MAX_REALM_PUBLIC_KEY_SIZE];
static size_t realm_attest_public_key_len;

/*
 * The hash of the realm attestation public key is included in the Platform
 * attestation token as the challenge claim.
 */
/* coverity[misra_c_2012_rule_12_1_violation:SUPPRESS] */
static uint8_t realm_attest_public_key_hash[PSA_HASH_LENGTH(PSA_ALG_SHA_256)];
static size_t realm_attest_public_key_hash_len;

/*
 * The key handle for the sign operation
 * When ATTEST_EL3_TOKEN_SIGN is set, RMM will only have the public key.
 * Else the flag indicates that the Private key is initialized.
 */
static bool attest_key_loaded; /* = false */
static psa_key_handle_t imported_key;

/*
 * Specify the hash algorithm to use for computing the hash of the
 * realm public key.
 */
static enum hash_algo public_key_hash_algo_id = HASH_SHA_256;

/*
 * TODO: review panic usage and try to gracefully exit on error. Also
 * improve documentation of usage of PSA APIs
 */
int attest_init_realm_attestation_key(void)
{
	psa_status_t psa_status;
	unsigned long ret;
	psa_key_attributes_t key_attributes = psa_key_attributes_init();
	struct t_cose_key attest_key;
	enum t_cose_err_t cose_res;
	struct q_useful_buf_c cose_key = {0};
	struct q_useful_buf cose_key_buf  = { realm_attest_public_key,
				      sizeof(realm_attest_public_key) };

	/*
	 * The realm attestation key is requested from the root world in the
	 * boot phase only once. Then the same key is used in the entire power
	 * cycle to sign the realm attestation tokens.
	 */
	if (attest_key_loaded) {
		ERROR("Realm attestation key already loaded.\n");
		return -EINVAL;
	}

#if ATTEST_EL3_TOKEN_SIGN

	ret = el0_app_service_call(APP_SERVICE_GET_REALM_ATTEST_PUB_KEY_FROM_EL3,
				   0, 0, 0, 0);
	if (ret > (unsigned long)INT_MAX) {
		return -EINVAL;
	}
	if (ret != 0U) {
		return (int)ret;
	}

	struct service_get_realm_attestation_pub_key_struct *attest_key_struct =
		(struct service_get_realm_attestation_pub_key_struct *)get_shared_mem_start();

	realm_attest_public_key_len = attest_key_struct->attest_pub_key_buf_size;
	(void)memcpy((void *)realm_attest_public_key,
		     attest_key_struct->attest_pub_key_buf,
		     realm_attest_public_key_len);

	/* Setup the key policy for public key */
	psa_set_key_usage_flags(&key_attributes, PSA_KEY_USAGE_SIGN_HASH);
	psa_set_key_algorithm(&key_attributes, PSA_ALG_ECDSA(PSA_ALG_SHA_384));
	psa_set_key_type(&key_attributes, PSA_KEY_TYPE_ECC_PUBLIC_KEY(PSA_ECC_FAMILY_SECP_R1));

	/* Import public key to mbed-crypto */
	psa_status = psa_import_key(&key_attributes,
				    realm_attest_public_key,
				    realm_attest_public_key_len,
				    &imported_key);
#else

	ret = el0_app_service_call(APP_SERVICE_GET_REALM_ATTESTATION_KEY,
				   0, 0, 0, 0);
	if (ret > (unsigned long)INT_MAX) {
		return -EINVAL;
	}
	if (ret != 0U) {
		return (int)ret;
	}

	struct service_get_realm_attestation_key_struct *attest_key_struct =
		(struct service_get_realm_attestation_key_struct *)get_shared_mem_start();

	/* Setup the key policy for private key */
	psa_set_key_usage_flags(&key_attributes, PSA_KEY_USAGE_SIGN_HASH);
	psa_set_key_algorithm(&key_attributes, PSA_ALG_ECDSA(PSA_ALG_SHA_384));
	psa_set_key_type(&key_attributes, PSA_KEY_TYPE_ECC_KEY_PAIR(PSA_ECC_FAMILY_SECP_R1));

	/* Import private key to mbed-crypto */
	psa_status = psa_import_key(&key_attributes,
			     (const uint8_t *)attest_key_struct->attest_key_buf,
			     attest_key_struct->attest_key_buf_size,
			     &imported_key);

	/* Clear the private key from the shared buffer */
	(void)memset(attest_key_struct->attest_key_buf, 0, attest_key_struct->attest_key_buf_size);
#endif

	if (psa_status != PSA_SUCCESS) {
		ERROR("psa_import_key has failed\n");
		psa_reset_key_attributes(&key_attributes);
		return -EINVAL;
	}

	/*
	 * Get the RMM public attestation key and encode it to a
	 * CBOR serialized COSE_Key object: RFC 8152, Section 7.
	 */
	attest_key.key.handle = imported_key;
	cose_res = t_cose_key_encode(attest_key,
				     cose_key_buf,
				     &cose_key);
	if (cose_res != T_COSE_SUCCESS) {
		ERROR("t_cose_key_encode has failed\n");
		psa_reset_key_attributes(&key_attributes);
		(void) psa_destroy_key(imported_key);
		return -EINVAL;
	}

	assert(cose_key.len != 0UL);
	realm_attest_public_key_len = cose_key.len;

	/* Compute the hash of the RMM public attestation key */
	psa_status = psa_hash_compute(PSA_ALG_SHA_256,
			       realm_attest_public_key,
			       realm_attest_public_key_len,
			       realm_attest_public_key_hash,
			       sizeof(realm_attest_public_key_hash),
			       &realm_attest_public_key_hash_len);
	if (psa_status != PSA_SUCCESS) {
		ERROR("psa_hash_compute has failed\n");
		psa_reset_key_attributes(&key_attributes);
		(void) psa_destroy_key(imported_key);
		return -EINVAL;
	}

	attest_key_loaded = true;
	return 0;
}

int attest_get_realm_signing_key(psa_key_handle_t *key_handle)
{
#if ATTEST_EL3_TOKEN_SIGN
	(void)key_handle;

	/* Trying to get signing key for EL3 token sign flow is invalid .*/
	return -EINVAL;
#else
	if (!attest_key_loaded) {
		ERROR("Realm attestation key not initialized\n");
		return -EINVAL;
	}

	*key_handle = imported_key;
	return 0;
#endif
}

/*
 * Get the hash of the realm attestation public key. The public key hash
 * is the challenge value in the platform attestation token.
 *
 * Arguments:
 * public_key_hash - Get the buffer address and size which holds
 *                   the hash of the realm attestation public key.
 *
 * Returns 0 on success, negative error code on error.
 *
 */
static int attest_get_realm_public_key_hash(
					struct q_useful_buf_c *public_key_hash)
{
	if (!attest_key_loaded) {
		ERROR("Realm attestation key not initialized\n");
		return -EINVAL;
	}

	public_key_hash->ptr = realm_attest_public_key_hash;
	public_key_hash->len = realm_attest_public_key_hash_len;
	return 0;
}

int attest_get_realm_public_key(struct q_useful_buf_c *public_key)
{
	if (!attest_key_loaded) {
		ERROR("Realm attestation key not initialized\n");
		return -EINVAL;
	}

	public_key->ptr = realm_attest_public_key;
	public_key->len = realm_attest_public_key_len;
	return 0;
}

int attest_setup_platform_token(void)
{
	void *shared_buf = get_shared_mem_start();
	size_t remaining_len = 0UL;
	struct q_useful_buf_c rmm_pub_key_hash;
	/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
	uint64_t hash_length;
	uint64_t offset = 0;
	int ret;

	/*
	 * Copy the RAK public hash value to the token buffer. This is
	 * used as the challenge input for the token generation
	 * thus creating a binding between the two.
	 */
	ret = attest_get_realm_public_key_hash(&rmm_pub_key_hash);
	if (ret != 0) {
		ERROR("Realm attestation key not initialized\n");
		return ret;
	}

	assert(rmm_pub_key_hash.ptr != NULL);
	(void)memcpy(shared_buf, rmm_pub_key_hash.ptr,
				 rmm_pub_key_hash.len);
	hash_length = rmm_pub_key_hash.len;

	struct service_get_platform_token_struct *service_get_platform_token_struct =
		(struct service_get_platform_token_struct *)get_shared_mem_start();

	do {
		size_t token_hunk_len;
		unsigned long uret;

		uret = el0_app_service_call(APP_SERVICE_GET_PLATFORM_TOKEN,
					hash_length, 0, 0, 0);

		if (uret != 0U) {
			return -EINVAL;
		}

		token_hunk_len = service_get_platform_token_struct->token_hunk_len;
		remaining_len = service_get_platform_token_struct->remaining_len;

		assert(token_hunk_len != 0UL);

		if ((offset + token_hunk_len + remaining_len)
				> ATTEST_PLAT_TOKEN_SIZE) {
			ERROR("Not enough space allocated to store token\n");
			return -ENOMEM;
		}

		/* coverity[misra_c_2012_rule_9_1_violation:SUPPRESS] */
		(void)memcpy((void *)&rmm_platform_token_buf[offset],
			     (void *)service_get_platform_token_struct->token_hunk_buf,
			     token_hunk_len);

		offset += token_hunk_len;

		/* Reset hash_length variable for the rest of the calls */
		hash_length = 0;
	} while (remaining_len > 0UL);

	rmm_platform_token.ptr = rmm_platform_token_buf;
	/*
	 * At this point, the offset value corresponds to the full
	 * length of the token received.
	 */
	rmm_platform_token.len = offset;

	return 0;
}

int attest_get_platform_token(const void **buf, size_t *len)
{
	assert(buf != NULL);
	assert(len != NULL);

	if (rmm_platform_token.ptr == NULL) {
		return -EINVAL;
	}

	*buf = rmm_platform_token.ptr;
	*len = rmm_platform_token.len;
	return 0;
}

enum hash_algo attest_get_realm_public_key_hash_algo_id(void)
{
	return public_key_hash_algo_id;
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <attestation.h>
#include <attestation_priv.h>
#include <debug.h>
#include <errno.h>
#include <measurement.h>
#include <psa/crypto.h>
#include <rmm_el3_ifc.h>
#include <simd.h>
#include <sizes.h>

#define ECC_P384_PUBLIC_KEY_SIZE	PSA_KEY_EXPORT_ECC_PUBLIC_KEY_MAX_SIZE(384)

/*
 * The size of X and Y coordinate in 2 parameter style EC public key. Format is
 * as defined in [COSE (RFC 8152)] (https://tools.ietf.org/html/rfc8152) and
 * [SEC 1: Elliptic Curve Cryptography](http://www.secg.org/sec1-v2.pdf).
 *
 * This size is well-known and documented in public standards.
 */
#define ECC_P384_COORD_SIZE	PSA_BITS_TO_BYTES(384)
#define BIT_SIZE_OF_P384	(384U)

/* ECC Curve type define for querying attestation key from monitor */
#define ATTEST_KEY_CURVE_ECC_SECP384R1	0

/*
 * The platform token which will be needed during attestation.
 */
static unsigned char rmm_platform_token_buf[SZ_4K];
static struct q_useful_buf rmm_platform_token;

/*
 * The public key is kept loaded as it is both not required to be secret (and
 * hence can be kept in attestation memory) and immutable.
 */
static uint8_t realm_attest_public_key[ECC_P384_PUBLIC_KEY_SIZE];
static size_t realm_attest_public_key_len;

/*
 * The hash of the realm attestation public key is included in the Platform
 * attestation token as the challenge claim.
 */
static uint8_t realm_attest_public_key_hash[PSA_HASH_LENGTH(PSA_ALG_SHA_256)];
static size_t realm_attest_public_key_hash_len;

/*
 * The key handle for the sign operation
 */
static bool attest_signing_key_loaded; /* = false */
static psa_key_handle_t attest_signing_key;

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
	psa_status_t ret;
	uintptr_t buf;
	size_t attest_key_size;
	psa_key_attributes_t key_attributes = psa_key_attributes_init();

	assert(SIMD_IS_FPU_ALLOWED());

	/*
	 * The realm attestation key is requested from the root world in the
	 * boot phase only once. Then the same key is used in the entire power
	 * cycle to sign the realm attestation tokens.
	 */
	if (attest_signing_key_loaded) {
		ERROR("Realm attestation key already loaded.\n");
		return -EINVAL;
	}

	/*
	 * Get the realm attestation key. The key is retrieved in raw format.
	 */
	buf = rmm_el3_ifc_get_shared_buf_locked();

	if (rmm_el3_ifc_get_realm_attest_key(buf,
				rmm_el3_ifc_get_shared_buf_size(),
				&attest_key_size,
				ATTEST_KEY_CURVE_ECC_SECP384R1) != 0) {
		rmm_el3_ifc_release_shared_buf();
		return -EINVAL;
	}

	/* Setup the key policy for private key */
	psa_set_key_usage_flags(&key_attributes, PSA_KEY_USAGE_SIGN_HASH);
	psa_set_key_algorithm(&key_attributes, PSA_ALG_ECDSA(PSA_ALG_SHA_384));
	psa_set_key_type(&key_attributes, PSA_KEY_TYPE_ECC_KEY_PAIR(PSA_ECC_FAMILY_SECP_R1));

	/* Import private key to mbed-crypto */
	/* coverity[misra_c_2012_rule_9_1_violation:SUPPRESS] */
	ret = psa_import_key(&key_attributes,
			     (const uint8_t *)buf,
			     attest_key_size,
			     &attest_signing_key);

	/* Clear the private key from the buffer */
	(void)memset((uint8_t *)buf, 0, attest_key_size);

	if (ret != PSA_SUCCESS) {
		return -EINVAL;
	}
	attest_signing_key_loaded = true;

	/* Get the RMM public attestation key */
	ret = psa_export_public_key(attest_signing_key,
				    realm_attest_public_key,
				    sizeof(realm_attest_public_key),
				    &realm_attest_public_key_len);
	if (ret != PSA_SUCCESS) {
		ERROR("psa_export_public_key has failed\n");
		rmm_el3_ifc_release_shared_buf();
		return -EINVAL;
	}

	/* Compute the hash of the RMM public attestation key */
	ret = psa_hash_compute(PSA_ALG_SHA_256,
			       realm_attest_public_key,
			       realm_attest_public_key_len,
			       realm_attest_public_key_hash,
			       sizeof(realm_attest_public_key_hash),
			       &realm_attest_public_key_hash_len);
	if (ret != PSA_SUCCESS) {
		ERROR("psa_hash_compute has failed\n");
		rmm_el3_ifc_release_shared_buf();
		return -EINVAL;
	}

	rmm_el3_ifc_release_shared_buf();

	return 0;
}

int attest_get_realm_signing_key(psa_key_handle_t *key_handle)
{
	if (!attest_signing_key_loaded) {
		ERROR("Realm attestation key not initialized\n");
		return -EINVAL;
	}

	*key_handle = attest_signing_key;
	return 0;
}

/*
 * Get the hash of the realm attestation public key. The public key hash is the
 * challenge value in the platform attestation token.
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
	if (!attest_signing_key_loaded) {
		ERROR("Realm attestation key not initialized\n");
		return -EINVAL;
	}

	public_key_hash->ptr = realm_attest_public_key_hash;
	public_key_hash->len = realm_attest_public_key_hash_len;
	return 0;
}

int attest_get_realm_public_key(struct q_useful_buf_c *public_key)
{
	if (!attest_signing_key_loaded) {
		ERROR("Realm attestation key not initialized\n");
		return -EINVAL;
	}

	public_key->ptr = realm_attest_public_key;
	public_key->len = realm_attest_public_key_len;
	return 0;
}

int attest_setup_platform_token(void)
{
	uintptr_t shared_buf;
	size_t platform_token_len;
	struct q_useful_buf_c rmm_pub_key_hash;
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

	shared_buf = rmm_el3_ifc_get_shared_buf_locked();

	(void)memcpy((void *)shared_buf, rmm_pub_key_hash.ptr,
					 rmm_pub_key_hash.len);

	ret = rmm_el3_ifc_get_platform_token(
			shared_buf,
			rmm_el3_ifc_get_shared_buf_size(),
			&platform_token_len,
			/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
			PSA_HASH_LENGTH(PSA_ALG_SHA_256));

	if (ret != 0) {
		rmm_el3_ifc_release_shared_buf();
		return -EINVAL;
	}

	/* coverity[misra_c_2012_rule_9_1_violation:SUPPRESS] */
	(void)memcpy((void *)rmm_platform_token_buf,
		     (void *)shared_buf,
		     platform_token_len);

	rmm_el3_ifc_release_shared_buf();

	rmm_platform_token.ptr = rmm_platform_token_buf;
	rmm_platform_token.len = platform_token_len;

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

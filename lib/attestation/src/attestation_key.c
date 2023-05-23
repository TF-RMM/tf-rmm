/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <attestation.h>
#include <attestation_priv.h>
#include <debug.h>
#include <errno.h>
#include <mbedtls/sha256.h>
#include <measurement.h>
#include <psa/crypto.h>
#include <rmm_el3_ifc.h>
#include <simd.h>
#include <sizes.h>

#define ECC_P384_PUBLIC_KEY_SIZE	(97U)
#define SHA256_DIGEST_SIZE		(32U)

/*
 * The size of X and Y coordinate in 2 parameter style EC public key. Format is
 * as defined in [COSE (RFC 8152)] (https://tools.ietf.org/html/rfc8152) and
 * [SEC 1: Elliptic Curve Cryptography](http://www.secg.org/sec1-v2.pdf).
 *
 * This size is well-known and documented in public standards.
 */
#define ECC_P384_COORD_SIZE		(48U) /* 384 bits -> 48 bytes */
#define BIT_SIZE_OF_P384		(384U)

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
static uint8_t realm_attest_public_key_hash[SHA256_DIGEST_SIZE];
static size_t realm_attest_public_key_hash_len;

/*
 * The keypair for the sign operation
 */
static mbedtls_ecp_keypair realm_attest_keypair = {0};

/* Specify the hash algorithm to use for computing the hash of the
 * realm public key.
 */
static enum hash_algo public_key_hash_algo_id = HASH_ALGO_SHA256;

/*
 * TODO: review panic usage and try to gracefully exit on error. Also
 * improve documentation of usage of MbedTLS APIs
 */
int attest_init_realm_attestation_key(void)
{
	int ret;
	struct q_useful_buf realm_attest_private_key;
	uintptr_t buf;
	size_t attest_key_size = 0UL;

	struct attest_rng_context rng_ctx;

	assert(SIMD_IS_FPU_ALLOWED());

	attest_get_cpu_rng_context(&rng_ctx);

	/*
	 * The realm attestation key is requested from the root world in the
	 * boot phase only once. Then the same key is used in the entire power
	 * cycle to sign the realm attestation tokens.
	 */
	if (realm_attest_keypair.MBEDTLS_PRIVATE(d).MBEDTLS_PRIVATE(p) != NULL) {
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

	realm_attest_private_key.len = attest_key_size;
	realm_attest_private_key.ptr = (void *)buf;

	/*
	 * Setup ECC key.
	 * The memory for the keypair is allocated from MbedTLS Heap.
	 */
	mbedtls_ecp_keypair_init(&realm_attest_keypair);
	ret = mbedtls_ecp_group_load(&realm_attest_keypair.MBEDTLS_PRIVATE(grp),
				     MBEDTLS_ECP_DP_SECP384R1);
	if (ret != 0) {
		ERROR("mbedtls_ecp_group_load has failed\n");
		rmm_el3_ifc_release_shared_buf();
		return -EINVAL;
	}

	ret = mbedtls_mpi_read_binary(&realm_attest_keypair.MBEDTLS_PRIVATE(d),
				      realm_attest_private_key.ptr,
				      realm_attest_private_key.len);
	if (ret != 0) {
		ERROR("mbedtls_mpi_read_binary has failed\n");
		rmm_el3_ifc_release_shared_buf();
		return -EINVAL;
	}

	ret = mbedtls_ecp_check_privkey(&realm_attest_keypair.MBEDTLS_PRIVATE(grp),
					&realm_attest_keypair.MBEDTLS_PRIVATE(d));
	if (ret != 0) {
		ERROR("mbedtls_ecp_check_privkey has failed: %d\n", ret);
		rmm_el3_ifc_release_shared_buf();
		return -EINVAL;
	}

	ret = mbedtls_ecp_mul(&realm_attest_keypair.MBEDTLS_PRIVATE(grp),
			      &realm_attest_keypair.MBEDTLS_PRIVATE(Q),
			      &realm_attest_keypair.MBEDTLS_PRIVATE(d),
			      &realm_attest_keypair.MBEDTLS_PRIVATE(grp).G,
			      rng_ctx.f_rng,
			      rng_ctx.p_rng);
	if (ret != 0) {
		ERROR("mbedtls_ecp_mul priv has failed: %d\n", ret);
		rmm_el3_ifc_release_shared_buf();
		return -EINVAL;
	}

	ret = mbedtls_ecp_point_write_binary(&realm_attest_keypair.MBEDTLS_PRIVATE(grp),
					     &realm_attest_keypair.MBEDTLS_PRIVATE(Q),
					     MBEDTLS_ECP_PF_UNCOMPRESSED,
					     &realm_attest_public_key_len,
					     realm_attest_public_key,
					     sizeof(realm_attest_public_key));
	if (ret != 0) {
		ERROR("mbedtls_ecp_point_write_binary pub has failed\n");
		rmm_el3_ifc_release_shared_buf();
		return -EINVAL;
	}

	/* Compute the hash of the realm attestation public key */
	ret = mbedtls_sha256(realm_attest_public_key,
			     realm_attest_public_key_len,
			     realm_attest_public_key_hash,
			     false);
	if (ret != 0) {
		ERROR("mbedtls_sha256 has failed\n");
		rmm_el3_ifc_release_shared_buf();
		return -EINVAL;
	}

	realm_attest_public_key_hash_len = sizeof(realm_attest_public_key_hash);

	/* Clear the private key from the buffer */
	(void)memset(realm_attest_private_key.ptr, 0,
			realm_attest_private_key.len);

	rmm_el3_ifc_release_shared_buf();

	return 0;
}

int attest_get_realm_signing_key(const void **keypair)
{
	if (realm_attest_keypair.MBEDTLS_PRIVATE(d).MBEDTLS_PRIVATE(p) == NULL) {
		ERROR("Realm attestation key not initialized\n");
		return -EINVAL;
	}

	*keypair = &realm_attest_keypair;
	return 0;
}

int attest_get_realm_public_key_hash(struct q_useful_buf_c *public_key_hash)
{
	if (realm_attest_keypair.MBEDTLS_PRIVATE(d).MBEDTLS_PRIVATE(p) == NULL) {
		ERROR("Realm attestation key not initialized\n");
		return -EINVAL;
	}

	public_key_hash->ptr = realm_attest_public_key_hash;
	public_key_hash->len = realm_attest_public_key_hash_len;
	return 0;
}

int attest_get_realm_public_key(struct q_useful_buf_c *public_key)
{
	if (realm_attest_keypair.MBEDTLS_PRIVATE(d).MBEDTLS_PRIVATE(p) == NULL) {
		ERROR("Realm attestation key not initialized\n");
		return -EINVAL;
	}

	public_key->ptr = realm_attest_public_key;
	public_key->len = realm_attest_public_key_len;
	return 0;
}

int attest_setup_platform_token(void)
{
	int ret;
	uintptr_t shared_buf;
	size_t platform_token_len = 0;
	struct q_useful_buf_c rmm_pub_key_hash;

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

	ret = rmm_el3_ifc_get_platform_token(shared_buf,
					     rmm_el3_ifc_get_shared_buf_size(),
					     &platform_token_len,
					     SHA256_DIGEST_SIZE);

	if (ret != 0) {
		rmm_el3_ifc_release_shared_buf();
		return -EINVAL;
	}

	(void)memcpy(rmm_platform_token_buf,
		     (void *)shared_buf,
		     platform_token_len);

	rmm_el3_ifc_release_shared_buf();

	rmm_platform_token.ptr = rmm_platform_token_buf;
	rmm_platform_token.len = platform_token_len;

	return 0;
}

int attest_get_platform_token(struct q_useful_buf_c **buf)
{
	assert(buf != NULL);

	if (rmm_platform_token.ptr == NULL) {
		return -EINVAL;
	}

	*buf = (struct q_useful_buf_c *)&rmm_platform_token;
	return 0;
}

enum hash_algo attest_get_realm_public_key_hash_algo_id(void)
{
	return public_key_hash_algo_id;
}

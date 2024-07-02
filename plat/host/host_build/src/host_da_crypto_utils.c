/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <debug.h>
#include <host_crypto_utils.h>
#include <mbedtls/asn1.h>
#include <mbedtls/bignum.h>
#include <mbedtls/ecdh.h>
#include <mbedtls/memory_buffer_alloc.h>
#include <mbedtls/rsa.h>
#include <mbedtls/x509.h>
#include <mbedtls/x509_crt.h>
#include <sizes.h>
#include <string.h>

#define HOST_MBEDTLS_HEAP_SIZE	(2U * SZ_4K)

static unsigned char host_mbedtls_heap[HOST_MBEDTLS_HEAP_SIZE];

static int host_get_leaf_cert_from_cert_chain(uint8_t *cert_chain,
					      size_t cert_chain_len,
					      uint8_t **leaf_cert,
					      size_t *leaf_cert_len)
{
	size_t asn1_len;
	unsigned char *tag_ptr;
	uint8_t *cert_chain_end;
	uint8_t *cur_cert;
	size_t cur_cert_len;
	int cur_cert_idx;
	int rc;

	cur_cert = cert_chain;
	cur_cert_idx = -1;
	cert_chain_end = cert_chain + cert_chain_len;
	cur_cert_len = 0;

	/* Get leaf certificate from cert_chain */
	while (true) {
		tag_ptr = cur_cert;
		rc = mbedtls_asn1_get_tag(&tag_ptr, cert_chain_end, &asn1_len,
					  MBEDTLS_ASN1_CONSTRUCTED |
					  MBEDTLS_ASN1_SEQUENCE);
		if (rc != 0) {
			break;
		}

		cur_cert_len = asn1_len + (tag_ptr - cur_cert);
		if (cur_cert + cur_cert_len > cert_chain_end) {
			cur_cert_idx = -1;
			break;
		}

		cur_cert = cur_cert + cur_cert_len;
		cur_cert_idx++;
	}

	if (cur_cert_idx == -1) {
		return -1;
	}

	*leaf_cert = cur_cert - cur_cert_len;
	*leaf_cert_len = cur_cert_len;
	INFO("leaf_cert_len: 0x%lx\n", *leaf_cert_len);

	return 0;
}

/*
 * @In:
 * cert_chain		- Certificate chain
 * cert_chain_len	- Length of certificate
 * public_key_len	- Max length of 'public_key' buffer
 * metadata_len		- Max length of 'metadata' buffer
 *
 * On success below variables are set:
 * @Out:
 * public_key		- Public key content
 * public_key_len	- length of 'public_key'
 * metadata		- Public key metadata content
 * metadata_len		- length of 'metadata' if metadata exists, else set to 0
 * public_key_algo	- Public key algorithm
 */
static int _host_get_public_key_from_cert_chain(uint8_t *cert_chain,
						size_t cert_chain_len,
						void *public_key,
						size_t *public_key_len,
						void *public_key_metadata,
						size_t *public_key_metadata_len,
						uint8_t *public_key_algo)
{
	uint8_t *leaf_cert;
	size_t leaf_cert_len;
	mbedtls_x509_crt crt;
	mbedtls_pk_type_t pk_type;
	int rc;

	/* Get leaf cert and its length */
	rc = host_get_leaf_cert_from_cert_chain(cert_chain, cert_chain_len,
						&leaf_cert, &leaf_cert_len);
	if (rc != 0) {
		return -1;
	}

	/* Get public key from leaf certificate */
	mbedtls_x509_crt_init(&crt);

	if (mbedtls_x509_crt_parse_der(&crt, leaf_cert, leaf_cert_len) != 0) {
		return -1;
	}

	pk_type = mbedtls_pk_get_type(&crt.pk);
	if (pk_type != MBEDTLS_PK_ECKEY && pk_type != MBEDTLS_PK_RSA) {
		rc = -1;
		goto out_crt_free;
	}

	if (pk_type == MBEDTLS_PK_ECKEY) {
		mbedtls_ecp_keypair *ecp;
		mbedtls_ecp_group grp;
		mbedtls_ecp_point pt;

		ecp = mbedtls_pk_ec(crt.pk);
		mbedtls_ecp_group_init(&grp);
		mbedtls_ecp_point_init(&pt);
		rc = mbedtls_ecp_export(ecp, &grp, NULL, &pt);

		if (rc != 0 || (grp.id != MBEDTLS_ECP_DP_SECP256R1 &&
				grp.id != MBEDTLS_ECP_DP_SECP384R1)) {
			mbedtls_ecp_point_free(&pt);
			mbedtls_ecp_group_free(&grp);
			rc = -1;
			goto out_crt_free;
		}

		rc = mbedtls_ecp_point_write_binary(&grp, &pt,
						    MBEDTLS_ECP_PF_UNCOMPRESSED,
						    public_key_len, public_key,
						    MBEDTLS_ECP_MAX_PT_LEN);

		if (rc == 0) {
			if (grp.id == MBEDTLS_ECP_DP_SECP256R1) {
				*public_key_algo =
					PUBLIC_KEY_ALGO_ECDSA_ECC_NIST_P256;
			} else {
				*public_key_algo =
					PUBLIC_KEY_ALGO_ECDSA_ECC_NIST_P384;
			}

			/* No metadata for PK_ECKEY type */
			*public_key_metadata_len = 0;
		}

		mbedtls_ecp_point_free(&pt);
		mbedtls_ecp_group_free(&grp);
	} else {
		mbedtls_rsa_context *rsa;
		mbedtls_mpi N;
		mbedtls_mpi E;
		size_t N_sz, E_sz;

		rsa = mbedtls_pk_rsa(crt.pk);
		mbedtls_mpi_init(&N);
		mbedtls_mpi_init(&E);

		rc = mbedtls_rsa_export(rsa, &N, NULL, NULL, NULL, &E);
		N_sz = mbedtls_mpi_size(&N);
		E_sz = mbedtls_mpi_size(&E);
		INFO("RSA public key len: %ld, metadata len:%ld\n", N_sz, E_sz);

		/* Supported ALGO type RSASSA_3072 (384 bytes) */
		if (rc == 0 && N_sz == 384) {
			rc = mbedtls_mpi_write_binary(&N, public_key, N_sz);
			rc |= mbedtls_mpi_write_binary(&E, public_key_metadata,
						       E_sz);
			if (rc == 0) {
				*public_key_algo = PUBLIC_KEY_ALGO_RSASSA_3072;
				*public_key_len = N_sz;
				*public_key_metadata_len = E_sz;
			}
		} else {
			rc = -1;
		}

		mbedtls_mpi_free(&N);
		mbedtls_mpi_free(&E);
	}

out_crt_free:
	mbedtls_x509_crt_free(&crt);

	return rc;
}

int host_get_public_key_from_cert_chain(uint8_t *cert_chain,
					size_t cert_chain_len,
					void *public_key,
					size_t *public_key_len,
					void *public_key_metadata,
					size_t *public_key_metadata_len,
					uint8_t *public_key_algo)
{
	int rc;

	mbedtls_memory_buffer_alloc_init(host_mbedtls_heap,
					 sizeof(host_mbedtls_heap));

	rc = _host_get_public_key_from_cert_chain(cert_chain, cert_chain_len,
						  public_key, public_key_len,
						  public_key_metadata,
						  public_key_metadata_len,
						  public_key_algo);

	mbedtls_memory_buffer_alloc_free();

	return rc;
}

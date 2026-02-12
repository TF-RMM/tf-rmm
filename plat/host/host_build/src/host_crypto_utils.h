/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_CRYPTO_UTILS_H
#define HOST_CRYPTO_UTILS_H

#define PUBLIC_KEY_ALGO_ECDSA_ECC_NIST_P256	0x10
#define PUBLIC_KEY_ALGO_ECDSA_ECC_NIST_P384	0x20
#define PUBLIC_KEY_ALGO_RSASSA_3072		0x30

int host_get_public_key_from_cert_chain(uint8_t *cert_chain,
					size_t cert_chain_len,
					void *public_key,
					size_t *public_key_len,
					void *public_key_metadata,
					size_t *public_key_metadata_len,
					uint8_t *public_key_algo);

#endif /* HOST_CRYPTO_UTILS_H */

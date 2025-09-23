/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ATTEST_DEFS_H
#define ATTEST_DEFS_H

#include <assert.h>
#include <sizes.h>
#include <smc-rmi.h>
#include <stdbool.h>
#include <stddef.h>
#include <utils_def.h>

#define ATTESTATION_APP_FUNC_ID_GLOBAL_INIT			27
#define ATTESTATION_APP_FUNC_ID_DO_HASH				33
#define ATTESTATION_APP_FUNC_ID_EXTEND_MEASUREMENT		93
#define ATTESTATION_APP_FUNC_ID_TOKEN_SIGN			107
#define ATTESTATION_APP_FUNC_ID_DO_CCA_TOKEN_CREATION		111
#define ATTESTATION_APP_FUNC_ID_TOKEN_CTX_INIT			113
#define ATTESTATION_APP_FUNC_ID_REALM_TOKEN_CREATE		114
#define EL3_TOKEN_WRITE_RESPONSE_TO_CTX				115

/* RmmHashAlgorithm type as per RMM spec */
enum hash_algo {
	HASH_SHA_256 = RMI_HASH_SHA_256,
	HASH_SHA_512 = RMI_HASH_SHA_512,
};

/* Size in bytes of the SHA256 measurement */
#define SHA256_SIZE			(32U)

/* Size in bytes of the SHA512 measurement */
#define SHA512_SIZE			(64U)

#ifndef CBMC
/*
 * Buffer size for CCA attestation token. Allocated on the attestation app heap
 * area.
 */
#define ATTEST_TOKEN_BUF_SIZE	(RMM_CCA_TOKEN_BUFFER * SZ_4K)
/*
 * Size in bytes of the largest measurement type that can be supported.
 * This macro needs to be updated accordingly if new algorithms are supported.
 */
#define MAX_MEASUREMENT_SIZE		SHA512_SIZE
#define ATTEST_CHALLENGE_SIZE		(64)
#define RMM_REALM_TOKEN_BUF_SIZE	SZ_1K
#else
#define ATTEST_TOKEN_BUF_SIZE	4U
#define MAX_MEASUREMENT_SIZE		sizeof(uint64_t)
#define ATTEST_CHALLENGE_SIZE		(1)
#define RMM_REALM_TOKEN_BUF_SIZE	4U

#endif

/* Maximum number of measurements */
#define MEASUREMENT_SLOT_NR		(5U)

/* Measurement slot reserved for RIM */
#define RIM_MEASUREMENT_SLOT		(0U)

#ifndef CBMC
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
#else /* CBMC */
enum attest_token_err_t {
	/* Success */
	ATTEST_TOKEN_ERR_SUCCESS = 0,
	ATTEST_TOKEN_ERR_INVALID_STATE,
	ATTEST_TOKEN_ERR_TOO_SMALL,
	/*
	 * Signing is in progress, function should be called with the same
	 * parameters again.
	 */
	ATTEST_TOKEN_ERR_COSE_SIGN_IN_PROGRESS
};
#endif /* CBMC */

/*
 * Return the hash size in bytes for the selected measurement algorithm.
 *
 * Arguments:
 *	- algorithm:	Algorithm to check.
 */
/* coverity[misra_c_2012_rule_5_9_violation:SUPPRESS] */
static inline size_t measurement_get_size(const enum hash_algo algorithm)
{
	size_t ret = 0UL;

	switch (algorithm) {
	case HASH_SHA_256:
		ret = (size_t)SHA256_SIZE;
		break;
	case HASH_SHA_512:
		ret = (size_t)SHA512_SIZE;
		break;
	default:
		assert(false);
	}

	return ret;
}

struct attest_heap_shared{
	uint8_t cca_attest_token_buf[ATTEST_TOKEN_BUF_SIZE];
};

struct attest_extend_measurement_buffers {
	size_t current_measurement_buf_offset;
	size_t current_measurement_buf_size;
	size_t extend_measurement_buf_offset;
	size_t extend_measurement_buf_size;
	uint8_t buf[GRANULE_SIZE - 32U];
};
COMPILER_ASSERT(sizeof(struct attest_extend_measurement_buffers) == GRANULE_SIZE);

struct attest_extend_measurement_return_buffer {
	size_t measurement_size;
	uint8_t measurement_buf[GRANULE_SIZE - 8U];
};
COMPILER_ASSERT(sizeof(struct attest_extend_measurement_return_buffer) == GRANULE_SIZE);

struct attest_realm_token_create_params {
	uint8_t measurements[MEASUREMENT_SLOT_NR][MAX_MEASUREMENT_SIZE];
	uint8_t rpv[RPV_SIZE];
	bool is_pvt_mecid;
	uint8_t challenge[ATTEST_CHALLENGE_SIZE];
};
COMPILER_ASSERT(sizeof(struct attest_realm_token_create_params) <= GRANULE_SIZE);

#endif /* ATTEST_DEFS_H */

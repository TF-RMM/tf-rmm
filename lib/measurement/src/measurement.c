/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <mbedtls/sha256.h>
#include <mbedtls/sha512.h>
#include <measurement.h>
#include <simd.h>
#include <stdbool.h>

#if LOG_LEVEL >= LOG_LEVEL_VERBOSE
static void measurement_print(unsigned char *measurement,
			      const enum hash_algo algorithm)
{
	unsigned int size = 0U;
	assert(measurement != NULL);

	VERBOSE("Measurement ");

	switch (algorithm) {
	case HASH_ALGO_SHA256:
		VERBOSE("(SHA256): 0x");
		size = SHA256_SIZE;
		break;
	case HASH_ALGO_SHA512:
		VERBOSE("(SHA512): 0x");
		size = SHA512_SIZE;
		break;
	default:
		/* Prevent static check and MISRA warnings */
		assert(false);
	}

	for (unsigned int i = 0U; i < size; ++i) {
		VERBOSE("%02x", *(measurement+i));
	}
	VERBOSE("\n");
}
#endif /* LOG_LEVEL */

static void do_hash(enum hash_algo hash_algo,
		    void *data,
		    size_t size,
		    unsigned char *out)
{
	__unused int ret;

	assert(size <= GRANULE_SIZE);
	assert((data != NULL) && (out != NULL));

	fpu_save_my_state();

	if (hash_algo == HASH_ALGO_SHA256) {
		/* 0 to indicate SHA256 not SHA224 */
		FPU_ALLOW(ret = mbedtls_sha256(data, size, out, 0));

		assert(ret == 0);
	} else if (hash_algo == HASH_ALGO_SHA512) {
		/* 0 to indicate SHA512 not SHA384 */
		FPU_ALLOW(ret = mbedtls_sha512(data, size, out, 0));

		assert(ret == 0);
	} else {
		assert(false);
	}

	fpu_restore_my_state();

#if LOG_LEVEL >= LOG_LEVEL_VERBOSE
	measurement_print(out, hash_algo);
#endif
}

void measurement_hash_compute(enum hash_algo hash_algo,
			      void *data,
			      size_t size,
			      unsigned char *out)
{
	do_hash(hash_algo, data, size, out);
}

static void measurement_extend_sha256(void *current_measurement,
				      size_t current_measurement_size,
				      void *extend_measurement,
				      size_t extend_measurement_size,
				      unsigned char *out)
{
	mbedtls_sha256_context sha256_ctx;

	__unused int ret = 0;

	mbedtls_sha256_init(&sha256_ctx);
	/* 0 to indicate SHA256 not SHA224 */
	ret = mbedtls_sha256_starts(&sha256_ctx, 0);
	assert(ret == 0);

	/* Update the measurement */
	ret = mbedtls_sha256_update(
		&sha256_ctx,
		(unsigned char *)current_measurement,
		current_measurement_size);
	assert(ret == 0);

	ret = mbedtls_sha256_update(&sha256_ctx,
					(unsigned char *)extend_measurement,
					extend_measurement_size);
	assert(ret == 0);

	ret = mbedtls_sha256_finish(&sha256_ctx, out);
	assert(ret == 0);
}

static void measurement_extend_sha512(void *current_measurement,
				      size_t current_measurement_size,
				      void *extend_measurement,
				      size_t extend_measurement_size,
				      unsigned char *out)
{
	mbedtls_sha512_context sha512_ctx;
	__unused int ret = 0;

	mbedtls_sha512_init(&sha512_ctx);
	/* 0 to indicate SHA256 not SHA384 */
	ret = mbedtls_sha512_starts(&sha512_ctx, 0);
	assert(ret == 0);

	/* Update the measurement */
	ret = mbedtls_sha512_update(
		&sha512_ctx,
		(unsigned char *)current_measurement,
		current_measurement_size);
	assert(ret == 0);

	ret = mbedtls_sha512_update(
		&sha512_ctx,
		(unsigned char *)extend_measurement_size,
		extend_measurement_size);
	assert(ret == 0);

	ret = mbedtls_sha512_finish(&sha512_ctx, out);
	assert(ret == 0);
}

void measurement_extend(enum hash_algo hash_algo,
			void *current_measurement,
			void *extend_measurement,
			size_t extend_measurement_size,
			unsigned char *out)
{
	size_t current_measurement_size = measurement_get_size(hash_algo);

	/* We limit the maximum size of the payload to be of GRANULE_SIZE */
	assert(current_measurement != NULL);
	assert(extend_measurement_size <= GRANULE_SIZE);
	assert(extend_measurement != NULL);
	assert(out != NULL);

	fpu_save_my_state();

	switch (hash_algo) {
	case HASH_ALGO_SHA256:
		FPU_ALLOW(
			measurement_extend_sha256(current_measurement,
					  current_measurement_size,
					  extend_measurement,
					  extend_measurement_size,
					  out));
		break;
	case HASH_ALGO_SHA512:
		FPU_ALLOW(
			measurement_extend_sha512(current_measurement,
					  current_measurement_size,
					  extend_measurement,
					  extend_measurement_size,
					  out));
		break;
	default:
		assert(false);
	}

	fpu_restore_my_state();

#if LOG_LEVEL >= LOG_LEVEL_VERBOSE
	measurement_print(out, hash_algo);
#endif
}

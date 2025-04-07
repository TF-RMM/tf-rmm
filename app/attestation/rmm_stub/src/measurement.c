/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <attest_app.h>
#include <debug.h>
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
	case HASH_SHA_256:
		VERBOSE("(SHA256): 0x");
		size = SHA256_SIZE;
		break;
	case HASH_SHA_512:
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

static void do_hash(enum hash_algo algorithm,
		    void *data,
		    size_t size,
		    unsigned char *out)
{
	attest_do_hash((unsigned int)algorithm, data, size, out);

#if LOG_LEVEL >= LOG_LEVEL_VERBOSE
	measurement_print(out, algorithm);
#endif
}

void measurement_hash_compute(enum hash_algo algorithm,
			      void *data,
			      size_t size,
			      unsigned char *out)
{
	do_hash(algorithm, data, size, out);
}

static void do_extend(void *app_data_cfg,
		      enum hash_algo algorithm,
		      void *current_measurement,
		      void *extend_measurement,
		      size_t extend_measurement_size,
		      unsigned char *out,
		      size_t out_size)
{
	attest_do_extend(app_data_cfg,
		      algorithm,
		      current_measurement,
		      extend_measurement,
		      extend_measurement_size,
		      out,
		      out_size);
}

void measurement_extend(void *app_data_cfg,
			enum hash_algo algorithm,
			void *current_measurement,
			void *extend_measurement,
			size_t extend_measurement_size,
			unsigned char *out,
			size_t out_size)
{
	/* We limit the maximum size of the payload to be of GRANULE_SIZE */
	assert(current_measurement != NULL);
	assert(extend_measurement_size <= GRANULE_SIZE);
	assert(extend_measurement != NULL);
	assert(out != NULL);

	do_extend(app_data_cfg,
			algorithm,
			current_measurement,
			extend_measurement,
			extend_measurement_size,
			out,
			out_size);

#if LOG_LEVEL >= LOG_LEVEL_VERBOSE
	measurement_print(out, algorithm);
#endif
}

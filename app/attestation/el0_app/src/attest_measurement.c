/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_common.h>
#include <assert.h>
#include <attest_defs.h>
#include <attest_measurement.h>
#include <import_sym.h>
#include <psa/crypto.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <utils_def.h>

/* cppcheck-suppress misra-c2012-8.7 */
unsigned long app_do_hash(enum hash_algo algorithm,
		    size_t size,
		    uint8_t *shared)
{
	__unused int ret;

	psa_algorithm_t psa_algorithm = PSA_ALG_NONE;
	size_t hash_size;
	uint8_t buf[SHA512_SIZE];

	assert(size <= GRANULE_SIZE);

	if (algorithm == HASH_SHA_256) {
		psa_algorithm = PSA_ALG_SHA_256;
	} else if (algorithm == HASH_SHA_512) {
		psa_algorithm = PSA_ALG_SHA_512;
	} else {
		assert(false);
	}

	/* coverity[misra_c_2012_rule_12_1_violation:SUPPRESS] */
	assert((size_t)PSA_HASH_LENGTH(psa_algorithm) <= sizeof(buf));

	ret = psa_hash_compute(psa_algorithm,
			shared,
			size,
			buf,
			/* coverity[misra_c_2012_rule_12_1_violation:SUPPRESS] */
			(size_t)PSA_HASH_LENGTH(psa_algorithm),
			&hash_size);

	/* coverity[uninit_use:SUPPRESS] */
	/* coverity[misra_c_2012_rule_12_1_violation:SUPPRESS] */
	assert(hash_size == (size_t)PSA_HASH_LENGTH(psa_algorithm));
	assert(ret == 0);
	/* coverity[uninit_use_in_call:SUPPRESS] */
	(void)memcpy(shared, buf, hash_size);

	return hash_size;
}

/* cppcheck-suppress misra-c2012-8.7 */
unsigned long app_do_extend(enum hash_algo algorithm,
		      size_t extend_measurement_size,
		      uint8_t *shared)
{
	psa_algorithm_t psa_algorithm = PSA_ALG_NONE;
	size_t hash_size;
	__unused psa_status_t ret;
	psa_hash_operation_t operation = PSA_HASH_OPERATION_INIT;
	size_t current_measurement_size;

	switch (algorithm) {
	case HASH_SHA_256:
		psa_algorithm = PSA_ALG_SHA_256;
		break;
	case HASH_SHA_512:
		psa_algorithm = PSA_ALG_SHA_512;
		break;
	default:
		assert(false);
	}

	/* coverity[misra_c_2012_rule_12_1_violation:SUPPRESS] */
	current_measurement_size = (size_t)PSA_HASH_LENGTH(psa_algorithm);

	struct attest_extend_measurement_buffers *buffers =
		(struct attest_extend_measurement_buffers *)shared;
	struct attest_extend_measurement_return_buffer *ret_buffer =
		(struct attest_extend_measurement_return_buffer *)shared;

	size_t ret_buf_size = sizeof(ret_buffer->measurement_buf);

	ret = psa_hash_setup(&operation, psa_algorithm);
	assert(ret == PSA_SUCCESS);

	assert(current_measurement_size <= buffers->current_measurement_buf_size);
	assert(extend_measurement_size <= buffers->extend_measurement_buf_size);

	ret = psa_hash_update(&operation,
			      &buffers->buf[buffers->current_measurement_buf_offset],
			      current_measurement_size);
	assert(ret == PSA_SUCCESS);

	ret = psa_hash_update(&operation,
			      &buffers->buf[buffers->extend_measurement_buf_offset],
			      extend_measurement_size);
	assert(ret == PSA_SUCCESS);

	ret = psa_hash_finish(&operation,
			      ret_buffer->measurement_buf,
			      ret_buf_size,
			      &hash_size);

	/* coverity[uninit_use:SUPPRESS] */
	/* coverity[misra_c_2012_rule_12_1_violation:SUPPRESS] */
	assert(hash_size == (size_t)PSA_HASH_LENGTH(psa_algorithm));
	assert(ret == PSA_SUCCESS);

	ret_buffer->measurement_size = hash_size;

	return hash_size;
}

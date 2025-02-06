/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ATTEST_DEFS_H
#define ATTEST_DEFS_H

#include <utils_def.h>
#include <stddef.h>

#define ATTESTATION_APP_FUNC_ID_INIT			10
#define ATTESTATION_APP_FUNC_ID_DO_HASH			33
#define ATTESTATION_APP_FUNC_ID_EXTEND_MEASUREMENT	93

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

#endif /* ATTEST_DEFS_H */

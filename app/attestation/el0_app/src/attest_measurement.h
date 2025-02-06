/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ATTEST_MEASUREMENT_H
#define ATTEST_MEASUREMENT_H

#include <attest_defs.h>
#include <stddef.h>

unsigned long app_do_hash(enum hash_algo algorithm, size_t size, uint8_t *shared);
unsigned long app_do_extend(enum hash_algo algorithm,
	size_t extend_measurement_size,
	uint8_t *shared);

#endif /* ATTEST_MEASUREMENT_H */

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include "measurement.h"
#include "tb_measurement.h"

bool valid_hash_algo(enum hash_algo value)
{
	return value == RMI_HASH_SHA_256 ||
	       value == RMI_HASH_SHA_512;
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ENTROPY_H
#define ENTROPY_H

#include <stdbool.h>
#include <stdint.h>

static inline bool arch_collect_entropy(uint64_t *random)
{
	static uint64_t val;

	*random = val++;
	return true;
}

#endif /* ENTROPY_H */

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ENTROPY_H
#define ENTROPY_H

#include <stdbool.h>
#include <stdint.h>

extern uint64_t entropy_val;

static inline void arch_reset_entropy(void)
{
	entropy_val = 0U;
}

static inline bool arch_collect_entropy(uint64_t *random)
{
	*random = entropy_val++;
	return true;
}

#endif /* ENTROPY_H */

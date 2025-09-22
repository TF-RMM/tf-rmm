/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TYPES_H
#define TYPES_H

#include <stdint.h>

typedef uint64_t u_register_t;

struct reg128 {
	unsigned long lo;
	unsigned long hi;
};

#endif /* TYPES_H */

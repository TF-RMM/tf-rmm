/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef FEATURE_H
#define FEATURE_H

#include <arch.h>

bool validate_feature_register(unsigned long index, unsigned long value);

#endif /* FEATURE_H */

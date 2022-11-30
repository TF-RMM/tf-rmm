/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef CPUID_H
#define CPUID_H

#include <arch_helpers.h>

static inline unsigned int my_cpuid(void)
{
	return (unsigned int)read_tpidr_el2();
}

#endif /* CPUID_H */

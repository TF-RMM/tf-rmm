/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef EL0_APP_HELPERS_ARCH_H
#define EL0_APP_HELPERS_ARCH_H

#include <stddef.h>

void *get_heap_start(void);
size_t get_heap_size(void);

#endif /* EL0_APP_HELPERS_ARCH_H */


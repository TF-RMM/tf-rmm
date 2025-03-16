/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef EL0_APP_HELPERS_ARCH_H
#define EL0_APP_HELPERS_ARCH_H

#include <stddef.h>

void *get_heap_start(void);
size_t get_heap_size(void);

/*
 * This function must be defined by all the apps. this should return the number
 * of pages allocated for instance specific heap for an app instance.
 */
size_t get_heap_page_count(void);

#endif /* EL0_APP_HELPERS_ARCH_H */


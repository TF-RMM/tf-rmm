/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef EL0_APP_HELPERS_H
#define EL0_APP_HELPERS_H

#include <stddef.h>

/*
 * This function must be defined by the app that uses Mbed TLS allocator
 *
 * The function returns the start address to a buffer_alloc_ctx object.
 */
void *mbedtls_app_get_heap(void);

#endif /* EL0_APP_HELPERS_H */


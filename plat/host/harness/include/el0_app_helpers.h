/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef EL0_APP_HELPERS_H
#define EL0_APP_HELPERS_H

#include <stddef.h>

/*
 * This function must be defined for Mbed TLS allocator.
 * The host build platform includes MbedTLS and hence this
 * header and function must be provided.
 *
 * The function returns the start address to a buffer_alloc_ctx object.
 */
void *mbedtls_app_get_heap(void);

#endif /* EL0_APP_HELPERS_H */


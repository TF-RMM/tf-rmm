/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <debug.h>

void mbedtls_exit_panic(unsigned int reason);

/* Used by Mbed TLS buffer alloc */
void mbedtls_exit_panic(unsigned int reason)
{
	(void) reason;
	panic();
}

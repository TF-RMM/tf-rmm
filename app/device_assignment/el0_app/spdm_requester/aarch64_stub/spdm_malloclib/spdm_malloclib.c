/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <base.h>
#include <library/malloclib.h>
#include <mbedtls/platform.h>
#include <string.h>

/*
 * Memory allocation used by libspdm. Before calling libspdm layer that might
 * result in memory alloction/free, it is the caller responsibility to set up the
 * allocation context (heap).
 */
/* cppcheck-suppress misra-c2012-8.7 */
void *allocate_pool(size_t AllocationSize)
{
	return mbedtls_calloc(1, AllocationSize);
}

/* cppcheck-suppress misra-c2012-8.7 */
void *allocate_zero_pool(size_t AllocationSize)
{
	void *buffer;

	buffer = mbedtls_calloc(1, AllocationSize);
	if (buffer == NULL) {
		return NULL;
	}
	(void)memset(buffer, 0, AllocationSize);

	return buffer;
}

/* cppcheck-suppress misra-c2012-8.7 */
void free_pool(void *buffer)
{
	mbedtls_free(buffer);
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <base.h>
#include <library/malloclib.h>
#include <memory_alloc.h>
#include <string.h>

/*
 * Memory allocation used by libspdm. Before calling libspdm layer that might
 * result in memory alloction/free, it is the caller responsibility to set up the
 * allocation context (heap).
 */
void *allocate_pool(size_t AllocationSize)
{
	return buffer_alloc_calloc(1, AllocationSize);
}

void *allocate_zero_pool(size_t AllocationSize)
{
	void *buffer;

	buffer = buffer_alloc_calloc(1, AllocationSize);
	if (buffer == NULL) {
		return NULL;
	}
	(void)memset(buffer, 0, AllocationSize);

	return buffer;
}

void free_pool(void *buffer)
{
	buffer_alloc_free(buffer);
}
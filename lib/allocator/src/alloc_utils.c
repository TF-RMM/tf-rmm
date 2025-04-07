/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <alloc_utils.h>
#include <assert.h>
#include <mbedtls/memory_buffer_alloc.h>
#include <memory_alloc.h>
#include <stddef.h>
#include <utils_def.h>

int alloc_heap_ctx_init(unsigned char *buf, size_t buf_size)
{
	assert(buf != NULL);

	/* Initialise the mbedTLS heap */
	mbedtls_memory_buffer_alloc_init(buf, buf_size);

	return 0;
}

void alloc_heap_ctx_assign_pe(struct rmm_buffer_alloc_ctx *ctx)
{
	int ret __unused;

	assert(ctx != NULL);

	/* Associate the buffer_alloc_ctx to this CPU */
	ret = buffer_alloc_ctx_assign(ctx);
	assert(ret == 0);
}

void alloc_heap_ctx_unassign_pe(void)
{
	buffer_alloc_ctx_unassign();
}

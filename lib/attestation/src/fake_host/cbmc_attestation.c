/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <memory_alloc.h>
#include <stdbool.h>
#include <stddef.h>
#include <tb_common.h>

int attestation_init(void)
{
	ASSERT(false, "attestation_init");
	return 0;
}

int attestation_heap_ctx_init(unsigned char *buf, size_t buf_size)
{
	ASSERT(false, "attestation_heap_ctx_init");
	return 0;
}

void attestation_heap_ctx_assign_pe(struct buffer_alloc_ctx *ctx)
{
	ASSERT(false, "attestation_heap_ctx_assign_pe");
}

void attestation_heap_ctx_unassign_pe(void)
{
	ASSERT(false, "attestation_heap_ctx_unassign_pe");
}

#endif /* CBMC */

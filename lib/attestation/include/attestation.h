/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ATTESTATION_H
#define ATTESTATION_H

#include <stddef.h>

struct buffer_alloc_ctx;

/*
 * Performs any early initialization needed for the crypto library.
 */
int attestation_init(void);

/*
 * Initialize the heap buffer to be used with the given buffer_alloc_ctx.
 * This is done when a REC is created.
 *
 * As a pre-requisite, ensure that a buffer_alloc_ctx has been assigned to this
 * PE prior to calling this function.
 *
 * Arguments:
 * buf - pointer to start of heap
 * buf_size -  size of the heap
 *
 * Returns 0 on success, negative error code on error.
 */
int attestation_heap_ctx_init(unsigned char *buf, size_t buf_size);

/*
 * Assign a given buf_alloc_ctx to this CPU. This needs to be called
 * prior to entering a Realm to allow it invoking RMM crypto operations.
 *
 * Arguments:
 * ctx - pointer to buffer_alloc_ctx
 */
void attestation_heap_ctx_assign_pe(struct buffer_alloc_ctx *ctx);


/*
 * Unassign a given buf_alloc_ctx from CPU. This needs to be called
 * after exiting the realm.
 *
 * Arguments:
 * ctx - pointer to buffer_alloc_ctx
 */
void attestation_heap_ctx_unassign_pe(void);

#endif /* ATTESTATION_H */

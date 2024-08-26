/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef MEMORY_ALLOC_H
#define MEMORY_ALLOC_H

#include <stddef.h>

typedef struct memory_header_s memory_header_t;


struct buffer_alloc_ctx {
	unsigned char		*buf;
	size_t			len;
	memory_header_t		*first;
	memory_header_t		*first_free;
	unsigned int		verify;
};

struct memory_header_s {
	size_t			magic1;
	size_t			size;
	size_t			alloc;
	memory_header_t		*prev;
	memory_header_t		*next;
	memory_header_t		*prev_free;
	memory_header_t		*next_free;
	size_t			magic2;
};

/*
 * Function to assign a heap context to the current CPU for
 * use by the MbedCrypto. In case the heap needs to be isolated
 * to the CPU executing a realm , this function must to be
 * called before entering a Realm. This will ensure that any
 * crypto operations triggered via RSI will used the assigned
 * heap.
 * Arguments:
 *  ctx - Pointer to a valid context for the memory allocator.
 * Returns:
 *  0 on success or a POSIX error code or error.
 */
int buffer_alloc_ctx_assign(struct buffer_alloc_ctx *ctx);

/*
 * Function to unasign a heap context from the current CPU.
 * In case the heap was isolated to the CPU executing a realm,
 * this function must to be called after exiting a Realm.
 */
void buffer_alloc_ctx_unassign(void);

#endif /* MEMORY_ALLOC_H */

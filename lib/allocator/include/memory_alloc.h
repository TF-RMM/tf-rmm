/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef MEMORY_ALLOC_H
#define MEMORY_ALLOC_H

#include <stddef.h>

typedef struct memory_header_s memory_header_t;

#ifndef CBMC

/* MbedTLS needs 8K of heap for attestation usecases */
#define REC_HEAP_PAGES			2U
#define REC_HEAP_SIZE			(REC_HEAP_PAGES * SZ_4K)

/* Number of pages per REC for PMU state */
#define REC_PMU_PAGES			1U
#define REC_PMU_SIZE			(REC_PMU_PAGES * SZ_4K)

/*
 * SIMD context that holds FPU/SVE registers. Space to save max arch supported
 * SVE vector length of 2048 bits.
 * Size of 32 Z registers (256 bytes each): 8192 bytes
 * Size of 16 P registers (32 bytes each) :  512 bytes
 * Size of 1 FFR register (32 bytes each) :   32 bytes
 * Size of other status registers         :   32 bytes
 * Total size is ~3 Pages (rounded up to page size).
 */
#define REC_SIMD_PAGES			3U
#define REC_SIMD_SIZE			(REC_SIMD_PAGES * SZ_4K)

/* Number of pages per REC for 'rec_attest_data' structure */
#define REC_ATTEST_PAGES		1U
#define REC_ATTEST_SIZE			(REC_ATTEST_PAGES * SZ_4K)

/* Number of pages per REC for attestation buffer */
#define REC_ATTEST_TOKEN_BUF_SIZE	(RMM_CCA_TOKEN_BUFFER * SZ_4K)

/* Number of pages per REC to be allocated */
#define REC_NUM_PAGES		(REC_HEAP_PAGES	  + \
				 REC_PMU_PAGES	  + \
				 REC_SIMD_PAGES	  + \
				 REC_ATTEST_PAGES + \
				 RMM_CCA_TOKEN_BUFFER)

#else /* CBMC */

#define REC_HEAP_PAGES		2U
#define REC_HEAP_SIZE		(REC_HEAP_PAGES * SZ_4K)

#define REC_PMU_PAGES		0U
#define REC_PMU_SIZE		(REC_PMU_PAGES * SZ_4K)

#define REC_SIMD_PAGES		0U
#define REC_SIMD_SIZE		(REC_SIMD_PAGES * SZ_4K)

#define REC_ATTEST_PAGES	0U
#define REC_ATTEST_SIZE		(REC_ATTEST_PAGES * SZ_4K)

/* Number of aux granules pages per REC to be used */
#define REC_NUM_PAGES		(1U)

#endif /* CBMC */

struct buffer_alloc_ctx {
	unsigned char		*buf;
	size_t			len;
	memory_header_t		*first;
	memory_header_t		*first_free;
	int			verify;
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

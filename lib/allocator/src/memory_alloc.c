/*
 * SPDX-License-Identifier: Apache-2.0
 * SPDX-FileCopyrightText: Copyright The Mbed TLS Contributors
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <cpuid.h>
#include <debug.h>
#include <errno.h>
#include <mbedtls/memory_buffer_alloc.h>
#include <mbedtls/platform.h>
#include <memory_alloc.h>
#include <sizes.h>
#include <string.h>

#define MAGIC1		UL(0xFF00AA55)
#define MAGIC2		UL(0xEE119966)
#define MAX_BT		20

#if defined(MBEDTLS_MEMORY_DEBUG)
#error MBEDTLS_MEMORY_DEBUG is not supported by this allocator.
#endif

#if defined(MBEDTLS_MEMORY_BUFFER_ALLOC_C)
/*
 * If MBEDTLS_MEMORY_BUFFER_ALLOC_C is defined then the allocator from mbedTLS
 * is going to be used, which is not desired.
 */
#error MBEDTLS_MEMORY_BUFFER_ALLOC_C is defined
#endif /* MBEDTLS_MEMORY_BUFFER_ALLOC_C */

#if defined(MBEDTLS_MEMORY_BACKTRACE)
#error MBEDTLS_MEMORY_BACKTRACE is not supported by this allocator.
#endif /* MBEDTLS_MEMORY_BACKTRACE */

#if defined(MBEDTLS_THREADING_C)
/*
 * This allocator doesn't support multithreading. On the other hand it
 * handles multiple heaps
 */
#error MBEDTLS_THREADING_C is not supported by this allocator.
#endif /* MBEDTLS_THREADING_C */

#if defined(MBEDTLS_SELF_TEST)
#error MBEDTLS_SELF_TEST is not supported by this allocator.
#endif /* MBEDTLS_SELF_TEST */

/* Array of heaps per CPU */
static struct buffer_alloc_ctx *ctx_per_cpu[MAX_CPUS];

static inline struct buffer_alloc_ctx *get_heap_ctx(void)
{
	struct buffer_alloc_ctx *ctx;
	unsigned int cpu_id = my_cpuid();

	assert(cpu_id < MAX_CPUS);

	ctx = ctx_per_cpu[cpu_id];
	/* Programming error if heap is not assigned */
	if (ctx == NULL) {
		ERROR(" No heap assigned to this CPU %u\n", cpu_id);
		panic();
	}

	return ctx;
}

static int verify_header(struct memory_header_s *hdr)
{
	if (hdr->magic1 != MAGIC1) {
		return 1;
	}

	if (hdr->magic2 != MAGIC2) {
		return 1;
	}

	if (hdr->alloc > 1UL) {
		return 1;
	}

	if ((hdr->prev != NULL) && (hdr->prev == hdr->next)) {
		return 1;
	}

	if ((hdr->prev_free != NULL) && (hdr->prev_free == hdr->next_free))	{
		return 1;
	}

	return 0;
}

static int verify_chain(struct buffer_alloc_ctx *heap)
{
	struct memory_header_s *prv = heap->first;
	struct memory_header_s *cur;

	if ((prv == NULL) || (verify_header(prv) != 0)) {
		return 1;
	}

	if (heap->first->prev != NULL) {
		return 1;
	}

	cur = heap->first->next;

	while (cur != NULL) {
		if (verify_header(cur) != 0) {
			return 1;
		}

		if (cur->prev != prv) {
			return 1;
		}

		prv = cur;
		cur = cur->next;
	}

	return 0;
}

static void *buffer_alloc_calloc_with_heap(struct buffer_alloc_ctx *heap,
					   size_t n,
					   size_t size)
{
	struct memory_header_s *new;
	struct memory_header_s *cur = heap->first_free;
	uintptr_t p;
	void *ret;
	size_t original_len;
	size_t len;

	if ((heap->buf == NULL) || (heap->first == NULL)) {
		return NULL;
	}

	original_len = n * size;
	len = original_len;

	if ((n == 0UL) || (size == 0UL) || ((len / n) != size)) {
		return NULL;
	} else if (len > ((size_t)-MBEDTLS_MEMORY_ALIGN_MULTIPLE)) {
		return NULL;
	}

	if ((len % U(MBEDTLS_MEMORY_ALIGN_MULTIPLE)) != 0U) {
		len -= len % U(MBEDTLS_MEMORY_ALIGN_MULTIPLE);
		len += U(MBEDTLS_MEMORY_ALIGN_MULTIPLE);
	}

	/* Find block that fits */
	while (cur != NULL) {
		if (cur->size >= len) {
			break;
		}
		cur = cur->next_free;
	}

	if (cur == NULL) {
		return NULL;
	}

	if (cur->alloc != 0UL) {
		assert(false);
	}

	/* Found location, split block if > memory_header + 4 room left */
	if ((cur->size - len) <
	   (sizeof(struct memory_header_s) + U(MBEDTLS_MEMORY_ALIGN_MULTIPLE))) {
		cur->alloc = 1UL;

		/* Remove from free_list */
		if (cur->prev_free != NULL) {
			cur->prev_free->next_free = cur->next_free;
		} else {
			heap->first_free = cur->next_free;
		}

		if (cur->next_free != NULL) {
			cur->next_free->prev_free = cur->prev_free;
		}

		cur->prev_free = NULL;
		cur->next_free = NULL;

		/* cppcheck-suppress misra-c2012-10.1 */
		if ((heap->verify & U(MBEDTLS_MEMORY_VERIFY_ALLOC)) != 0U) {
			assert(verify_chain(heap) == 0);
		}

		ret = (void *)((uintptr_t)cur + sizeof(struct memory_header_s));
		(void)memset(ret, 0, original_len);

		return ret;
	}

	p = ((uintptr_t)cur) + sizeof(struct memory_header_s) + len;
	new = (struct memory_header_s *) p;

	new->size = cur->size - len - sizeof(struct memory_header_s);
	new->alloc = 0;
	new->prev = cur;
	new->next = cur->next;
	new->magic1 = MAGIC1;
	new->magic2 = MAGIC2;

	if (new->next != NULL) {
		new->next->prev = new;
	}

	/* Replace cur with new in free_list */
	new->prev_free = cur->prev_free;
	new->next_free = cur->next_free;
	if (new->prev_free != NULL) {
		new->prev_free->next_free = new;
	} else {
		heap->first_free = new;
	}

	if (new->next_free != NULL) {
		new->next_free->prev_free = new;
	}

	cur->alloc = 1;
	cur->size = len;
	cur->next = new;
	cur->prev_free = NULL;
	cur->next_free = NULL;

	/* cppcheck-suppress misra-c2012-10.1 */
	if ((heap->verify & U(MBEDTLS_MEMORY_VERIFY_ALLOC)) != 0U) {
		assert(verify_chain(heap) == 0);
	}

	ret = (void *)((uintptr_t)cur + sizeof(struct memory_header_s));
	(void)memset(ret, 0, original_len);

	return ret;
}

void *buffer_alloc_calloc(size_t n, size_t size)
{
	struct buffer_alloc_ctx *heap = get_heap_ctx();

	assert(heap);
	return buffer_alloc_calloc_with_heap(heap, n, size);
}

static void buffer_alloc_free_with_heap(struct buffer_alloc_ctx *heap,
					void *ptr)
{
	struct memory_header_s *hdr;
	struct memory_header_s *old = NULL;
	uintptr_t p = (uintptr_t)ptr;

	if ((ptr == NULL) || (heap->buf == NULL) || (heap->first == NULL)) {
		return;
	}

	if ((p < (uintptr_t)heap->buf) || (p >= ((uintptr_t)heap->buf + heap->len))) {
		assert(0);
	}

	p -= sizeof(struct memory_header_s);
	hdr = (struct memory_header_s *) p;

	assert(verify_header(hdr) == 0);

	if (hdr->alloc != 1U) {
		assert(0);
	}

	hdr->alloc = 0;

	/* Regroup with block before */
	if ((hdr->prev != NULL) && (hdr->prev->alloc == 0UL)) {
		hdr->prev->size += sizeof(struct memory_header_s) + hdr->size;
		hdr->prev->next = hdr->next;
		old = hdr;
		hdr = hdr->prev;

		if (hdr->next != NULL) {
			hdr->next->prev = hdr;
		}

		(void)memset(old, 0, sizeof(struct memory_header_s));
	}

	/* Regroup with block after */
	if ((hdr->next != NULL) && (hdr->next->alloc == 0UL)) {
		hdr->size += sizeof(struct memory_header_s) + hdr->next->size;
		old = hdr->next;
		hdr->next = hdr->next->next;

		if ((hdr->prev_free != NULL) || (hdr->next_free != NULL)) {
			if (hdr->prev_free != NULL) {
				hdr->prev_free->next_free = hdr->next_free;
			} else {
				heap->first_free = hdr->next_free;
			}
			if (hdr->next_free != NULL) {
				hdr->next_free->prev_free = hdr->prev_free;
			}
		}

		hdr->prev_free = old->prev_free;
		hdr->next_free = old->next_free;

		if (hdr->prev_free != NULL) {
			hdr->prev_free->next_free = hdr;
		} else {
			heap->first_free = hdr;
		}

		if (hdr->next_free != NULL) {
			hdr->next_free->prev_free = hdr;
		}

		if (hdr->next != NULL) {
			hdr->next->prev = hdr;
		}

		(void)memset(old, 0, sizeof(struct memory_header_s));
	}

	/*
	 * Prepend to free_list if we have not merged
	 * (Does not have to stay in same order as prev / next list)
	 */
	if (old == NULL) {
		hdr->next_free = heap->first_free;
		if (heap->first_free != NULL) {
			heap->first_free->prev_free = hdr;
		}
		heap->first_free = hdr;
	}

	/* cppcheck-suppress misra-c2012-10.1 */
	if ((heap->verify & U(MBEDTLS_MEMORY_VERIFY_FREE)) != 0U) {
		assert(verify_chain(heap));
	}
}

void buffer_alloc_free(void *ptr)
{
	struct buffer_alloc_ctx *heap = get_heap_ctx();

	assert(heap);
	buffer_alloc_free_with_heap(heap, ptr);
}

int buffer_alloc_ctx_assign(struct buffer_alloc_ctx *ctx)
{
	unsigned int cpuid = my_cpuid();

	assert(cpuid < MAX_CPUS);

	if (ctx == NULL) {
		return -EINVAL;
	}

	if (ctx_per_cpu[cpuid] != NULL) {
		/* multiple assign */
		return -EINVAL;
	}

	ctx_per_cpu[cpuid] = ctx;

	return 0;
}

void buffer_alloc_ctx_unassign(void)
{
	unsigned int cpuid = my_cpuid();

	assert(cpuid < MAX_CPUS);

	/* multiple unassign */
	assert(ctx_per_cpu[cpuid] != NULL);

	ctx_per_cpu[cpuid] = NULL;
}

/* NOTE: This function is not currently expected to be called. */
void mbedtls_memory_buffer_set_verify(int verify)
{
	struct buffer_alloc_ctx *heap = get_heap_ctx();

	assert(heap);
	heap->verify = verify;
}

int mbedtls_memory_buffer_alloc_verify(void)
{
	struct buffer_alloc_ctx *heap = get_heap_ctx();

	assert(heap);
	return verify_chain(heap);
}

void mbedtls_memory_buffer_alloc_init(unsigned char *buf, size_t len)
{
	uintptr_t p = (uintptr_t)buf;

	/* The heap structure is obtained from the REC
	 * while the buffer is passed in the init function.
	 * This way the interface can remain the same.
	 */
	struct buffer_alloc_ctx *heap = get_heap_ctx();

	assert(heap);

	(void)memset(heap, 0, sizeof(struct buffer_alloc_ctx));

	if (len < sizeof(struct memory_header_s) +
	    U(MBEDTLS_MEMORY_ALIGN_MULTIPLE)) {
		return;
	} else if (((size_t)buf % U(MBEDTLS_MEMORY_ALIGN_MULTIPLE)) != 0U) {
		/* Adjust len first since buf is used in the computation */
		len -= U(MBEDTLS_MEMORY_ALIGN_MULTIPLE)
			- ((size_t)buf % U(MBEDTLS_MEMORY_ALIGN_MULTIPLE));
		p += U(MBEDTLS_MEMORY_ALIGN_MULTIPLE)
			- ((size_t)buf % U(MBEDTLS_MEMORY_ALIGN_MULTIPLE));
		buf = (unsigned char *)p;
	}

	(void)memset(buf, 0, len);

	heap->buf = buf;
	heap->len = len;

	heap->first = (struct memory_header_s *)buf;
	heap->first->size = len - sizeof(struct memory_header_s);
	heap->first->magic1 = MAGIC1;
	heap->first->magic2 = MAGIC2;
	heap->first_free = heap->first;
}

void mbedtls_memory_buffer_alloc_free(void)
{
	struct buffer_alloc_ctx *heap = get_heap_ctx();

	assert(heap);
	(void)memset(heap, 0, sizeof(struct buffer_alloc_ctx));
}

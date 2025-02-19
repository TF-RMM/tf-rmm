/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_common.h>
#include <assert.h>
#include <debug.h>
#include <el0_app_helpers.h>
#include <errno.h>
#include <mbedtls/hmac_drbg.h>
#include <mbedtls/memory_buffer_alloc.h>
#include <random_defs.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define PRNG_HEAP_SIZE	512U

struct random_heap_t {
	/* Variables that are not dynamically allocated, but need to be kept
	 * local to app instance.
	 */
	buffer_alloc_ctx mbedtls_heap_ctx;
	bool prng_init_done;
	mbedtls_hmac_drbg_context cpu_drbg_ctx;
	/* The actual heap buffer */
	unsigned char mbedtls_heap_buf[PRNG_HEAP_SIZE] __aligned(sizeof(unsigned long));
};

/* coverity[misra_c_2012_rule_5_8_violation:SUPPRESS] */
void *mbedtls_app_get_heap(void)
{
	return &((struct random_heap_t *)get_heap_start())->mbedtls_heap_ctx;
}

/* Make sure that the buffer used by the allocator is 64 bit dword aligned. */
COMPILER_ASSERT((U(offsetof(struct random_heap_t, mbedtls_heap_buf)) % sizeof(unsigned long)) == 0UL);

static int prng_init(size_t seed_len)
{
	/* The seed is expected to be populated in the shared buffer */
	uint8_t *seed = (uint8_t *)get_shared_mem_start();
	struct random_heap_t *heap = (struct random_heap_t *)get_heap_start();

	const mbedtls_md_info_t *md_info;
	int rc;

	if ((seed_len != 128UL) || (get_shared_mem_size() < seed_len)) {
		return - EINVAL;
	}

	assert(!heap->prng_init_done);

	mbedtls_memory_buffer_alloc_init(heap->mbedtls_heap_buf, sizeof(heap->mbedtls_heap_buf));
	md_info = mbedtls_md_info_from_type(MBEDTLS_MD_SHA256);
	mbedtls_hmac_drbg_init(&heap->cpu_drbg_ctx);
	rc = mbedtls_hmac_drbg_seed_buf(&heap->cpu_drbg_ctx, md_info,
					seed, seed_len);

	if (rc != 0) {
		return - EINVAL;
	}

	heap->prng_init_done = true;

	return 0;
}

static int prng_get_random(size_t output_size)
{
	int ret;
	void *rng_ctx;

	/* The output is copied in the shared buffer */
	uint8_t *output = (uint8_t *)get_shared_mem_start();
	struct random_heap_t *heap = (struct random_heap_t *)get_heap_start();

	if (output_size > get_shared_mem_size()) {
		return - EINVAL;
	}

	assert(heap->prng_init_done);

	rng_ctx = &heap->cpu_drbg_ctx;
	ret = mbedtls_hmac_drbg_random(rng_ctx, output, output_size);
	if (ret != 0) {
		return - EINVAL;
	}

	return 0;
}

/* coverity[misra_c_2012_rule_5_8_violation:SUPPRESS] */
unsigned long el0_app_entry_func(
	unsigned long func_id,
	unsigned long arg_0,
	unsigned long arg_1,
	unsigned long arg_2,
	unsigned long arg_3)
{
	unsigned long ret;

	(void)arg_1;
	(void)arg_2;
	(void)arg_3;

	switch (func_id) {
	case RANDOM_APP_FUNC_ID_PRNG_INIT:
		ret = (unsigned long)prng_init(arg_0);
		return ret;
	case RANDOM_APP_FUNC_ID_PRNG_GET_RANDOM:
		ret = (unsigned long)prng_get_random(arg_0);
		return ret;
	default:
		assert(false);
		return 0;
	}
}

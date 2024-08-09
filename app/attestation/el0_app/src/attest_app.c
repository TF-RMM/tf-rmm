/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

 #include <app_common.h>
 #include <arch.h>
 #include <arch_features.h>
 #include <assert.h>
 #include <attest_measurement.h>
 #include <errno.h>
 #include <mbedtls/memory_buffer_alloc.h>
 #include <psa/crypto.h>
 #include <stdbool.h>
 #include <stddef.h>
 #include <stdint.h>

/*
 * The heap buffer size used by the Mbed TLS allocator is calculated so that
 * attest_heap_t has the same size as HEAP_PAGE_COUNT * GRANULE_SIZE
 * fills the memory
 */
#define MBEDTLS_HEAP_BUF_SIZE				\
	((HEAP_PAGE_COUNT * GRANULE_SIZE) -		\
		(sizeof(buffer_alloc_ctx) +		\
		 sizeof(struct token_sign_cntxt) +	\
		 REC_ATTEST_TOKEN_BUF_SIZE +		\
		 RMM_REALM_TOKEN_BUF_SIZE +		\
		 sizeof(size_t)))

/* The following static variables are common for all attest app instances */
static bool attest_key_init_done;

/*
 * Variables that need to be allocated in the heap buffer
 * (Must be declared in struct attest_heap_t):
 */
struct attest_heap_t {
	/*
	 * Variables that are not dynamically allocated, but need to be kept
	 * local to app instance.
	 */
	/* The actual heap buffer */
	unsigned char mbedtls_heap_buf[MBEDTLS_HEAP_BUF_SIZE] __aligned(sizeof(unsigned long));
};
COMPILER_ASSERT(sizeof(struct attest_heap_t) == (HEAP_PAGE_COUNT * GRANULE_SIZE));

/* Make sure that the buffer used by the allocator is aligned */
COMPILER_ASSERT((UL(offsetof(struct attest_heap_t, mbedtls_heap_buf)) % sizeof(unsigned long)) == 0U);

/* coverity[misra_c_2012_rule_5_8_violation:SUPPRESS] */
unsigned long el0_app_entry_func(
	unsigned long func_id,
	unsigned long arg_0,
	unsigned long arg_1,
	unsigned long arg_2,
	unsigned long arg_3)
{
	void *shared = get_shared_mem_start();

	(void)arg_2;
	(void)arg_3;

	switch (func_id) {
	case ATTESTATION_APP_FUNC_ID_DO_HASH:
		return app_do_hash((enum hash_algo)arg_0, arg_1, (uint8_t *)shared);
	case ATTESTATION_APP_FUNC_ID_EXTEND_MEASUREMENT:
		return do_extend((int)arg_0, arg_1);
	default:
		assert(false);
		return 0;
	}
}

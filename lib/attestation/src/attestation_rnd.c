/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <assert.h>
#include <attestation.h>
#include <attestation_priv.h>
#include <cpuid.h>
#include <entropy.h>
#include <errno.h>
#include <fpu_helpers.h>
#include <mbedtls/entropy.h>
#include <mbedtls/hmac_drbg.h>
#include <platform_api.h>
#include <stdbool.h>
#include <utils_def.h>

/*
 * Allocate a PRNG object per PE in order to avoid the necessity of locking if
 * concurrent attestation token requests are executed.
 */
static mbedtls_hmac_drbg_context cpu_drbg_ctx[MAX_CPUS];
static bool prng_init_done;

static int get_random_seed(unsigned char *output, size_t len)
{
	uint64_t *random_output;
	uint64_t *random_end;

	assert(!prng_init_done);

	/* Enforce `len` is a multiple of 8 and `output` is 8-byte aligned. */
	assert((len & 0x7UL) == 0UL && ((uintptr_t)output & 0x7UL) == 0UL);

	random_output = (uint64_t *)output;
	random_end = (uint64_t *)(output + len);

	for (; random_output < random_end; ++random_output) {
		bool rc = false;

		rc = arch_collect_entropy(random_output);
		if (!rc) {
			return -EINVAL;
		}
	}
	return 0;
}

/*
 * This function is used by Mbed TLS as a source of entropy. This means it is
 * called during RMM operation, to add entropy to the signing process.
 * See declaration in mbedtls/entropy_poll.h.
 * For details see `MBEDTLS_ENTROPY_HARDWARE_ALT` in mbedtls/config.h
 */
int mbedtls_hardware_poll(void  *data, unsigned char *output,
			  size_t len,  size_t        *olen)
{
	int ret;
	unsigned int cpu_id = my_cpuid();
	void *rng_ctx;

	assert(prng_init_done);

	(void)data;

	/* Not in RMM init, PRNGs are already initialized, use them. */
	rng_ctx = &cpu_drbg_ctx[cpu_id];
	ret = mbedtls_hmac_drbg_random(rng_ctx, output, len);
	if (ret != 0) {
		return ret;
	}
	*olen = len;

	return 0;
}

void attest_get_cpu_rng_context(struct attest_rng_context *rng_ctx)
{
	unsigned int cpu_id = my_cpuid();

	assert(prng_init_done);

	rng_ctx->f_rng = mbedtls_hmac_drbg_random;
	rng_ctx->p_rng = &cpu_drbg_ctx[cpu_id];
}

int attest_rnd_prng_init(void)
{
	const mbedtls_md_info_t *md_info;
	mbedtls_hmac_drbg_context drbg_ctx;
	uint8_t seed[128] __aligned(8) ; /* mbedtls_hardware_poll request this size */
	unsigned int i;
	int rc;
	int retval = 0;

	assert(!prng_init_done);
	assert(IS_FPU_ALLOWED());

	if (!is_feat_rng_present()) {
		return -EINVAL;
	}

	/*
	 * Setup a temporary PRNG which seeded by real TRNG and use this
	 * instance to set up the per CPU PRNG objects. The temporary PRNG
	 * relies on the RNDR instruction to get its seed. RNDR instruction has
	 * an implementation defined TRNG backend. The timing of the TRNG could
	 * be nondeterministic therefore access to it is kept on the minimum.
	 */
	rc = get_random_seed(seed, sizeof(seed));
	if (rc != 0) {
		return -EINVAL;
	}

	md_info = mbedtls_md_info_from_type(MBEDTLS_MD_SHA256);
	mbedtls_hmac_drbg_init(&drbg_ctx);
	rc = mbedtls_hmac_drbg_seed_buf(&drbg_ctx,
				    md_info,
				    seed, sizeof(seed));
	if (rc != 0) {
		retval = -EINVAL;
		goto free_temp_prng;
	}

	/*
	 * Set up the per CPU PRNG objects which going to be used during
	 * Elliptic Curve signing to blind the private key.
	 */
	for (i = 0U; i < MAX_CPUS; ++i) {
		rc = mbedtls_hmac_drbg_random(&drbg_ctx, seed, sizeof(seed));
		if (rc != 0) {
			retval = -EINVAL;
			goto free_temp_prng;
		}

		mbedtls_hmac_drbg_init(&cpu_drbg_ctx[i]);
		rc = mbedtls_hmac_drbg_seed_buf(&cpu_drbg_ctx[i], md_info,
						seed, sizeof(seed));
		if (rc != 0) {
			retval = -EINVAL;
			goto free_temp_prng;
		}
	}

	prng_init_done = true;

free_temp_prng:
	/* Free the memory allocated by the temporary PRNG */
	mbedtls_hmac_drbg_free(&drbg_ctx);

	return retval;
}

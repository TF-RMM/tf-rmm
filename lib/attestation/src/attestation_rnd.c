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
#include <mbedtls/entropy.h>
#include <mbedtls/hmac_drbg.h>
#include <psa/crypto.h>
#include <simd.h>
#include <stdbool.h>
#include <utils_def.h>

/*
 * Allocate a PRNG object per PE in order to avoid the necessity of locking if
 * concurrent attestation token requests are executed.
 */
static mbedtls_hmac_drbg_context cpu_drbg_ctx[MAX_CPUS];
static bool prng_init_done;

static void get_random_seed(uintptr_t output, size_t len)
{
	assert(!prng_init_done);

	/* Enforce `len` is a multiple of 8 and `output` is 8-byte aligned. */
	assert(((len & 7UL) == 0UL) && ((output & 7UL) == 0UL));

	while (len != 0UL) {
		while (!arch_collect_entropy((uint64_t *)output)) {
		}

		len -= sizeof(uint64_t);
		output += sizeof(uint64_t);
	}
}

/*
 * This function is used by Mbed TLS as a source of entropy. This means it is
 * called during RMM operation, to add entropy to the signing process.
 * See declaration in ext/mbedtls/include/psa/crypto_extra.h.
 * For details see `MBEDTLS_PSA_CRYPTO_EXTERNAL_RNG` in mbedtls/mbedtls_config.h
 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
psa_status_t mbedtls_psa_external_get_random(
	mbedtls_psa_external_random_context_t *context,
	uint8_t *output, size_t output_size, size_t *output_length)
{
	int ret;
	unsigned int cpu_id = my_cpuid();
	void *rng_ctx;

	assert(prng_init_done);

	(void)context;

	/* Not in RMM init, PRNGs are already initialized, use them. */
	rng_ctx = &cpu_drbg_ctx[cpu_id];
	ret = mbedtls_hmac_drbg_random(rng_ctx, output, output_size);
	if (ret != 0) {
		return PSA_ERROR_HARDWARE_FAILURE;
	}
	*output_length = output_size;

	return PSA_SUCCESS;
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
	assert(SIMD_IS_FPU_ALLOWED());

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
	get_random_seed((uintptr_t)&seed, sizeof(seed));

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

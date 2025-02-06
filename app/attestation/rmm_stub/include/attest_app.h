/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ATTEST_APP_H
#define ATTEST_APP_H

#include <app.h>
#include <smc-rmi.h>
#include <stddef.h>

/* RmmHashAlgorithm type as per RMM spec */
enum hash_algo {
	HASH_SHA_256 = RMI_HASH_SHA_256,
	HASH_SHA_512 = RMI_HASH_SHA_512,
};

/* Size in bytes of the SHA256 measurement */
#define SHA256_SIZE			(32U)

/* Size in bytes of the SHA512 measurement */
#define SHA512_SIZE			(64U)

#ifndef CBMC
/*
 * Size in bytes of the largest measurement type that can be supported.
 * This macro needs to be updated accordingly if new algorithms are supported.
 */
#define MAX_MEASUREMENT_SIZE		SHA512_SIZE
#else
#define MAX_MEASUREMENT_SIZE		sizeof(uint64_t)
#endif

void attest_do_hash(unsigned int algorithm,
		    void *data,
		    size_t size,
		    unsigned char *out);
void attest_do_extend(struct app_data_cfg *app_data,
		      enum hash_algo algorithm,
		      void *current_measurement,
		      void *extend_measurement,
		      size_t extend_measurement_size,
		      unsigned char *out,
		      size_t out_size);

/* Init an app instance for this CPU */
void attest_app_init_per_cpu_instance(void);

#endif /* ATTEST_APP_H */

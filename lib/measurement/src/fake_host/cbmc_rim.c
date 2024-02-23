/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <measurement.h>
#include <stdbool.h>
#include <tb_common.h>

void measurement_data_granule_measure(unsigned char rim_measurement[],
				      enum hash_algo algorithm,
				      void *data,
				      unsigned long ipa,
				      unsigned long flags)
{
	ASSERT(false, "measurement_data_granule_measure");
}

void measurement_realm_params_measure(unsigned char rim_measurement[],
				      enum hash_algo algorithm,
				      struct rmi_realm_params *realm_params)
{
	ASSERT(false, "measurement_realm_params_measure");
}

void measurement_rec_params_measure(unsigned char rim_measurement[],
				    enum hash_algo algorithm,
				    struct rmi_rec_params *rec_params)
{
	ASSERT(false, "measurement_rec_params_measure");
}

void measurement_init_ripas_measure(unsigned char rim_measurement[],
				    enum hash_algo algorithm,
				    unsigned long ipa,
				    unsigned long level)
{
	ASSERT(false, "measurement_init_ripas_measure");
}

#endif /* CBMC */

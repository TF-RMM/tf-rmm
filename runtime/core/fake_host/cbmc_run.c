/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <rec.h>
#include <stdbool.h>
#include <tb_common.h>

void rec_run_loop(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	ASSERT(false, "rec_run_loop");
}

void inject_serror(struct rec *rec, unsigned long vsesr)
{
	ASSERT(false, "inject_serror");
}

void init_all_cpus_ns_simd_context(void)
{
	ASSERT(false, "init_all_cpus_ns_simd_context");
}

struct simd_context *get_cpu_ns_simd_context(void)
{
	ASSERT(false, "get_cpu_ns_simd_context");
	return NULL;
}

#endif /* CBMC */

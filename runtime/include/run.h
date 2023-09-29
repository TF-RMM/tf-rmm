/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RUN_H
#define RUN_H

struct rec;
struct simd_context;

/*
 * Function to enter Realm with `regs` pointing to GP Regs to be
 * restored/saved when entering/exiting the Realm. This function
 * returns with the Realm exception code which is populated by
 * Realm_exit() on aarch64.
 */
int run_realm(unsigned long *regs);

/* Initialize the NS world SIMD context for all CPUs. */
void init_all_cpus_ns_simd_context(void);

/* Returns current CPU's NS world SIMD context */
struct simd_context *get_cpu_ns_simd_context(void);

#endif /* RUN_H */

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RUN_H
#define RUN_H

#include <utils_def.h>

struct rec;
struct rec_plane;
struct simd_context;
STRUCT_TYPE sysreg_state;

/*
 * Function to enter Realm with `rec_regs` pointing to GP Regs to be
 * restored/saved when entering/exiting the Realm and rec_sp_el0 pointing
 * to the current plane sp_el0 register to be saved/restored. This function
 * returns with the Realm exception code which is populated by
 * Realm_exit() on aarch64.
 */
int run_realm(unsigned long *rec_regs, unsigned long *rec_sp_el0);

/* Initialize the NS world SIMD context for all CPUs. */
void init_all_cpus_ns_simd_context(void);

/* Returns current CPU's NS world SIMD context */
struct simd_context *get_cpu_ns_simd_context(void);

/* Restore the state @plane and @sysregs into the current realm */
void restore_realm_state(struct rec *rec, struct rec_plane *plane,
			STRUCT_TYPE sysreg_state *sysregs);

/* Save the realm state into @plane and @sysregs */
void save_realm_state(struct rec *rec, struct rec_plane *plane,
			STRUCT_TYPE sysreg_state *sysregs);

#endif /* RUN_H */

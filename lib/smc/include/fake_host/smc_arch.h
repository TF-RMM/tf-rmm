/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SMC_ARCH_H
#define SMC_ARCH_H

/* Result registers X0-X4 */
#define SMC_RESULT_REGS		5U

struct smc_result {
	unsigned long x[SMC_RESULT_REGS];
};

typedef unsigned long (*host_monitor_call_func)(unsigned long,
	unsigned long, unsigned long,
	unsigned long, unsigned long,
	unsigned long, unsigned long);

typedef void (*host_monitor_call_with_res_func)(unsigned long,
	unsigned long, unsigned long,
	unsigned long, unsigned long,
	unsigned long, unsigned long,
	struct smc_result *);

void register_host_monitor_functions(
	host_monitor_call_func monitor_call,
	host_monitor_call_with_res_func monitor_call_with_res);

#endif /* SMC_ARCH_H */
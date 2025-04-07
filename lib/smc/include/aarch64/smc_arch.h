/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SMC_ARCH_H
#define SMC_ARCH_H

/* Result registers X0-X4 */
#define SMC_RESULT_REGS		5U

#ifndef __ASSEMBLER__

struct smc_result {
	unsigned long x[SMC_RESULT_REGS];
};

#endif /* __ASSEMBLER__ */

#endif /* SMC_ARCH_H */
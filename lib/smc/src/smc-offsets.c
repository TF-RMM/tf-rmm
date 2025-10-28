/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <smc.h>
#include <stddef.h>
#include <utils_def.h>

COMPILER_ASSERT(sizeof(struct smc_args) == (sizeof(unsigned long) * 12U));
COMPILER_ASSERT(U(offsetof(struct smc_args, v)) == SMC_ARG_X1_X2);
COMPILER_ASSERT((U(offsetof(struct smc_args, v)) + U(16)) == SMC_ARG_X3_X4);
COMPILER_ASSERT((U(offsetof(struct smc_args, v)) + U(32)) == SMC_ARG_X5_X6);
COMPILER_ASSERT((U(offsetof(struct smc_args, v)) + U(48)) == SMC_ARG_X7_X8);
COMPILER_ASSERT((U(offsetof(struct smc_args, v)) + U(64)) == SMC_ARG_X9_X10);
COMPILER_ASSERT((U(offsetof(struct smc_args, v)) + U(80)) == SMC_ARG_X11_X12);
COMPILER_ASSERT(sizeof(((struct smc_args *)NULL)->v) == SMC_ARG_X11_X12 + U(16));

COMPILER_ASSERT(sizeof(struct smc_result) == (sizeof(unsigned long) * 5U));
COMPILER_ASSERT(U(offsetof(struct smc_result, x)) == SMC_RES_X0_X1);
COMPILER_ASSERT((U(offsetof(struct smc_result, x)) + U(16)) == SMC_RES_X2_X3);
COMPILER_ASSERT((U(offsetof(struct smc_result, x)) + U(32)) == SMC_RES_X4);
COMPILER_ASSERT(sizeof(((struct smc_result *)NULL)->x) == SMC_RES_X4 + U(8));

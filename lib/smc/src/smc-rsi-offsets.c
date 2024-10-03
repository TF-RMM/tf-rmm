/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <smc-rsi.h>
#include <stddef.h>
#include <utils_def.h>

COMPILER_ASSERT_NO_CBMC(sizeof(struct rsi_realm_config) == 0x1000UL);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rsi_realm_config, ipa_width)) == 0U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rsi_realm_config, algorithm)) == 8U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rsi_realm_config, rpv)) == 0x200U);

COMPILER_ASSERT_NO_CBMC(sizeof(struct rsi_host_call) == 0x100UL);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rsi_host_call, imm)) == 0U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rsi_host_call, gprs[0U])) == 8U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rsi_host_call,
			 gprs[RSI_HOST_CALL_NR_GPRS - 1U])) ==
			 U(8U * RSI_HOST_CALL_NR_GPRS));

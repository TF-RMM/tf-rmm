/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <smc-rsi.h>
#include <stddef.h>
#include <utils_def.h>

COMPILER_ASSERT(sizeof(struct rsi_realm_config) == 0x1000);
COMPILER_ASSERT(offsetof(struct rsi_realm_config, ipa_width) == 0);
COMPILER_ASSERT(offsetof(struct rsi_realm_config, algorithm) == 8);

COMPILER_ASSERT(sizeof(struct rsi_host_call) == 0x100);
COMPILER_ASSERT(offsetof(struct rsi_host_call, imm) == 0);
COMPILER_ASSERT(offsetof(struct rsi_host_call, gprs[0]) == 8);
COMPILER_ASSERT(offsetof(struct rsi_host_call,
			 gprs[RSI_HOST_CALL_NR_GPRS - 1]) ==
			 (8 * RSI_HOST_CALL_NR_GPRS));

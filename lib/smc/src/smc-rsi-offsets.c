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
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rsi_realm_config, num_aux_planes)) == 0x10U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rsi_realm_config, gicv3_vtr)) == 0x18U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rsi_realm_config, rpv)) == 0x200U);

COMPILER_ASSERT_NO_CBMC(sizeof(struct rsi_host_call) == 0x100UL);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rsi_host_call, imm)) == 0U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rsi_host_call, gprs[0U])) == 8U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rsi_host_call,
			 gprs[RSI_HOST_CALL_NR_GPRS - 1U])) ==
			 U(8U * RSI_HOST_CALL_NR_GPRS));

COMPILER_ASSERT(sizeof(struct rsi_plane_run) == 0x1000UL);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_run, enter)) == 0x0U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_run, exit)) == 0x800U);

COMPILER_ASSERT(sizeof(struct rsi_plane_enter) <
		U(offsetof(struct rsi_plane_run, exit)));
COMPILER_ASSERT(U(offsetof(struct rsi_plane_enter, flags)) == 0x0U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_enter, pc)) == 0x8U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_enter, pstate)) == 0x10U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_enter, gprs)) == 0x100U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_enter, gicv3_hcr)) == 0x200U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_enter, gicv3_lrs)) == 0x208U);

COMPILER_ASSERT(sizeof(struct rsi_plane_exit) <
		(sizeof(struct rsi_plane_run) -
		 U(offsetof(struct rsi_plane_run, exit))));
COMPILER_ASSERT(U(offsetof(struct rsi_plane_exit, reason)) == 0x0U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_exit, elr_el2)) == 0x100U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_exit, esr_el2)) == 0x108U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_exit, far_el2)) == 0x110U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_exit, hpfar_el2)) == 0x118U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_exit, pstate)) == 0x120U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_exit, gprs)) == 0x200U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_exit, gicv3_hcr)) == 0x300U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_exit, gicv3_lrs)) == 0x308U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_exit, gicv3_misr)) == 0x388U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_exit, gicv3_vmcr)) == 0x390U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_exit, cntp_ctl)) == 0x400U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_exit, cntp_cval)) == 0x408U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_exit, cntv_ctl)) == 0x410U);
COMPILER_ASSERT(U(offsetof(struct rsi_plane_exit, cntv_cval)) == 0x418U);

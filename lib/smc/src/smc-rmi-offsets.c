/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <smc-rmi.h>
#include <stddef.h>

COMPILER_ASSERT_NO_CBMC(sizeof(struct rmi_realm_params) == 0x1000UL);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_realm_params, flags)) == 0U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_realm_params, s2sz)) == 0x8U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_realm_params, sve_vl)) == 0x10U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_realm_params, num_bps)) == 0x18U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_realm_params, num_wps)) == 0x20U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_realm_params, pmu_num_ctrs)) == 0x28U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_realm_params, algorithm)) == 0x30U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_realm_params, rpv)) == 0x400U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_realm_params, vmid)) == 0x800U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_realm_params, rtt_base)) == 0x808U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_realm_params, rtt_level_start)) == 0x810U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_realm_params, rtt_num_start)) == 0x818U);

COMPILER_ASSERT_NO_CBMC(sizeof(struct rmi_rec_params) == 0x1000UL);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_params, flags)) == 0U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_params, mpidr)) == 0x100U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_params, pc)) == 0x200U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_params, gprs)) == 0x300U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_params, num_aux)) == 0x800U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_params, aux)) == 0x808U);

COMPILER_ASSERT_NO_CBMC(sizeof(struct rmi_rec_enter) == 0x800UL);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_enter, flags)) == 0U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_enter, gprs)) == 0x200U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_enter, gicv3_hcr)) == 0x300U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_enter, gicv3_lrs)) == 0x308U);

COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, exit_reason)) == 0U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, esr)) == 0x100U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, far)) == 0x108U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, hpfar)) == 0x110U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, gprs)) == 0x200U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, gicv3_hcr)) == 0x300U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, gicv3_lrs)) == 0x308U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, gicv3_misr)) == 0x388U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, gicv3_vmcr)) == 0x390U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, cntp_ctl)) == 0x400U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, cntp_cval)) == 0x408U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, cntv_ctl)) == 0x410U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, cntv_cval)) == 0x418U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, ripas_base)) == 0x500U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, ripas_top)) == 0x508U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, ripas_value)) == 0x510U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, imm)) == 0x600U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_exit, pmu_ovf_status)) == 0x700U);

COMPILER_ASSERT(sizeof(struct rmi_rec_run) <= GRANULE_SIZE);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_run, enter)) == 0U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct rmi_rec_run, exit)) == 0x800U);

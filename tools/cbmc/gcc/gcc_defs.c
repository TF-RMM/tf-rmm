/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <granule_types.h>
#include <smc-rmi.h>
#include <tb_granules.h>
#include <tb_common.h>
#include <tb_realm.h>
#include <tb_rec.h>

struct simd_context *simd_context_switch(struct simd_context *ctx_in,
					 struct simd_context *ctx_out)
{
	return 0;
}

enum s2_walk_status realm_ipa_to_pa(struct rec *rec,
				    unsigned long ipa,
				    struct s2_walk_result *s2_walk)
{
	volatile enum s2_walk_status s = WALK_SUCCESS;
	return s;
}

unsigned long nondet_unsigned_long(void)
{
	return 0UL;
}

unsigned int nondet_unsigned_int(void)
{
	return 0U;
}

size_t nondet_size_t(void)
{
	return (size_t)0;
}

struct granule nondet_struct_granule(void)
{
	struct granule g = {0};
	return g;
}

struct SPEC_granule nondet_struct_SPEC_granule(void)
{
	struct SPEC_granule g = {0};
	return g;
}

struct tb_regs nondet_tb_regs(void)
{
	struct tb_regs r = {0};
	return r;
}

struct rmi_realm_params nondet_struct_rmi_realm_params(void)
{
	struct rmi_realm_params p = {0};
	return p;
}

struct rmi_realm_params_buffer nondet_struct_rmi_realm_params_buffer(void)
{
	struct rmi_realm_params_buffer b = {0};
	return b;
}

struct rmm_realm nondet_struct_rmm_realm(void) {
	struct rmm_realm r = {0};
	return r;
}

struct rd nondet_struct_rd(void) {
	struct rd r = {0};
	return r;
}

struct simd_config nondet_simd_config(void) {
	struct simd_config s = {0};
	return s;
}

struct rmm_rec nondet_struct_rmm_rec(void) {
	struct rmm_rec r = {0};
	return r;
}

struct rec nondet_rec(void)
{
	struct rec r = {0};
	return r;
}

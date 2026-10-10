/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_helpers.h>
#include <buffer.h>
#include <esr.h>
#include <exit.h>
#include <granule.h>
#include <host_utils.h>
#include <psci.h>
#include <realm.h>
#include <rec.h>
}

#include "rmi_test_helpers.h"

/*
 * DEN0137 2.0-bet3 B6.3.1.2 target_match requires INVALID_PARAMETERS
 * when the MPIDR identifies no REC in the Realm. B6.3.1.3 not_runnable
 * reserves OFF for an existing REC that is not runnable.
 *
 * Create the Realm and RECs through RMI, including AUX donation and MPIDR
 * registration. Drive both PSCI calling conventions through the real exit
 * handler, then destroy the objects through RMI before resetting tracking.
 */
#define AFFINITY_TEST_SELF_MPIDR		0UL
#define AFFINITY_TEST_USED_MPIDR		1UL
#define AFFINITY_TEST_UNUSED_MPIDR	2UL
#define AFFINITY_TEST_GPR_MARKER		0xa5a5a5a5UL

/* Create a target REC with the requested runnable state through RMI. */
static void create_target_rec(struct rmi_test_realm *realm,
			      struct rmi_test_rec *target, bool runnable)
{
	struct smc_result res = {};
	struct rmi_rec_params *params;

	target->rec = realm->allocate(1U);
	target->params = realm->allocate(1U);
	rmi_test_delegate(target->rec, 1U);
	params = (struct rmi_rec_params *)target->params;
	(void)memset(params, 0, sizeof(*params));
	params->mpidr = AFFINITY_TEST_USED_MPIDR;
	params->flags = runnable ? REC_PARAMS_FLAG_RUNNABLE : 0UL;

	smc_rec_create(realm->rd, target->rec, target->params, &res);
	target->num_aux = rmi_test_complete_create(res, realm->addr_list,
		target->aux, MAX_REC_AUX_GRANULES, false, realm->allocate);
}

static void destroy_rec(struct rmi_test_realm *realm,
			struct rmi_test_rec *rec)
{
	struct smc_result res = {};

	if (rec->num_aux == 0U) {
		return;
	}

	smc_rec_destroy(rec->rec, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	rmi_test_reclaim(res.x[1], realm->addr_list, rec->num_aux);
	rec->num_aux = 0U;
}

struct affinity_test_context {
	struct rmi_test_realm realm;
	struct rmi_test_rec caller;
	struct rmi_test_rec target;
	struct granule *running_target;
};

TEST_GROUP(psci_affinity_info_tests) {
	struct affinity_test_context ctx;

	TEST_SETUP()
	{
		ctx = {};
		test_helpers_init();
		test_helpers_rmm_start(false);
		test_helpers_allocate_reset();
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
		LONGS_EQUAL(0, host_util_set_default_sysreg_cb((char *)"far_el2",
							     0UL));
		LONGS_EQUAL(0, host_util_set_default_sysreg_cb((char *)"hpfar_el2",
							     0UL));
		LONGS_EQUAL(0, host_util_set_default_sysreg_cb((char *)"par_el1",
							     0UL));
		LONGS_EQUAL(0, host_util_set_default_sysreg_cb((char *)"spsr_el2",
							     0UL));
	}

	TEST_TEARDOWN()
	{
		if (ctx.running_target != NULL) {
			atomic_granule_put_release(ctx.running_target);
		}
		destroy_rec(&ctx.realm, &ctx.target);
		destroy_rec(&ctx.realm, &ctx.caller);
		if (ctx.realm.num_aux != 0U) {
			rmi_test_realm_destroy(&ctx.realm);
		}
	}
};

static void build_realm(struct affinity_test_context *ctx,
			bool target_runnable)
{
	struct smc_result res = {};

	rmi_test_realm_prepare(&ctx->realm);
	rmi_test_realm_create(&ctx->realm);
	rmi_test_rec_create(&ctx->realm, &ctx->caller);
	create_target_rec(&ctx->realm, &ctx->target, target_runnable);
	smc_realm_activate(ctx->realm.rd, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
}

/* Model a running caller, with its REC and AUX mapped as on REC_ENTER. */
static void check_affinity_info(const struct affinity_test_context *ctx,
				unsigned long target_affinity,
				unsigned long lowest_affinity_level,
				unsigned long expected)
{
	const unsigned long fids[] = {
		SMC32_PSCI_AFFINITY_INFO, SMC64_PSCI_AFFINITY_INFO
	};
	struct granule *g_rec = tr_find_fine_granule(ctx->caller.rec);

	CHECK_TRUE(g_rec != NULL);
	for (unsigned int i = 0U; i < ARRAY_SIZE(fids); i++) {
		struct rmi_rec_exit rec_exit = {};
		struct rec *rec;
		struct rec_plane *plane;
		void *rec_aux;
		unsigned long result, marker, pc;
		bool resume;

		granule_lock(g_rec, GRANULE_STATE_REC);
		rec = (struct rec *)buffer_granule_map(g_rec, SLOT_REC);
		CHECK_TRUE(rec != NULL);
		atomic_granule_get(g_rec);
		granule_unlock(g_rec);
		rec_aux = buffer_rec_aux_granules_map(rec->g_aux, rec->num_rec_aux);
		CHECK_TRUE(rec_aux != NULL);
		plane = rec_plane_0(rec);
		plane->regs[0] = fids[i];
		plane->regs[1] = target_affinity;
		plane->regs[2] = lowest_affinity_level;
		plane->regs[4] = AFFINITY_TEST_GPR_MARKER;
		write_elr_el2(0x1000UL);
		write_esr_el2(ESR_EL2_EC_SMC | MASK(ESR_EL2_IL));

		resume = handle_realm_exit(rec, &rec_exit, ARM_EXCEPTION_SYNC_LEL);
		result = plane->regs[0];
		marker = plane->regs[4];
		pc = read_elr_el2();

		/* Release the caller before assertions so teardown can destroy it. */
		buffer_rec_aux_unmap(rec_aux, rec->num_rec_aux);
		buffer_unmap(rec);
		atomic_granule_put_release(g_rec);

		CHECK_TRUE(resume);
		UNSIGNED_LONGS_EQUAL(0x1004UL, pc);
		UNSIGNED_LONGS_EQUAL(AFFINITY_TEST_GPR_MARKER, marker);
		UNSIGNED_LONGS_EQUAL(expected, result);
	}
}

/* Control: the calling REC itself is on. */
TEST(psci_affinity_info_tests, self_is_on)
{
	build_realm(&ctx, false);
	check_affinity_info(&ctx, AFFINITY_TEST_SELF_MPIDR, 0UL,
			    PSCI_AFFINITY_INFO_ON);
}

/* B6.3.1.3 not_runnable: an existing REC that is off reports OFF. */
TEST(psci_affinity_info_tests, used_mpidr_not_runnable_is_off)
{
	build_realm(&ctx, false);
	check_affinity_info(&ctx, AFFINITY_TEST_USED_MPIDR, 0UL,
			    PSCI_AFFINITY_INFO_OFF);
}

/* B6.3.1.3 runnable: a different runnable REC reports ON. */
TEST(psci_affinity_info_tests, used_mpidr_runnable_is_on)
{
	build_realm(&ctx, true);
	check_affinity_info(&ctx, AFFINITY_TEST_USED_MPIDR, 0UL,
			    PSCI_AFFINITY_INFO_ON);
}

/* A target still executing CPU_OFF is ON until it drops its reference. */
TEST(psci_affinity_info_tests, used_mpidr_running_is_on)
{
	struct granule *g_target;

	build_realm(&ctx, false);
	g_target = tr_find_fine_granule(ctx.target.rec);
	CHECK_TRUE(g_target != NULL);
	granule_lock(g_target, GRANULE_STATE_REC);
	atomic_granule_get(g_target);
	granule_unlock(g_target);
	ctx.running_target = g_target;
	check_affinity_info(&ctx, AFFINITY_TEST_USED_MPIDR, 0UL,
			    PSCI_AFFINITY_INFO_ON);
	atomic_granule_put_release(g_target);
	ctx.running_target = NULL;
	check_affinity_info(&ctx, AFFINITY_TEST_USED_MPIDR, 0UL,
			    PSCI_AFFINITY_INFO_OFF);
}

/* B6.3.1.2 target_bound: a non-zero affinity level is rejected. */
TEST(psci_affinity_info_tests, nonzero_affinity_level_is_invalid)
{
	build_realm(&ctx, false);
	check_affinity_info(&ctx, AFFINITY_TEST_USED_MPIDR, 1UL,
			    PSCI_RETURN_INVALID_PARAMS);
}

/* B6.3.1.2 target_match: an MPIDR with no REC is INVALID_PARAMETERS. */
TEST(psci_affinity_info_tests, unused_mpidr_is_invalid_parameters)
{
	build_realm(&ctx, false);
	check_affinity_info(&ctx, AFFINITY_TEST_UNUSED_MPIDR, 0UL,
			    PSCI_RETURN_INVALID_PARAMS);
}

/* REC_DESTROY must remove the MPIDR mapping, even for a formerly runnable REC. */
TEST(psci_affinity_info_tests, destroyed_mpidr_is_invalid_parameters)
{
	build_realm(&ctx, true);
	check_affinity_info(&ctx, AFFINITY_TEST_USED_MPIDR, 0UL,
			    PSCI_AFFINITY_INFO_ON);
	destroy_rec(&ctx.realm, &ctx.target);
	check_affinity_info(&ctx, AFFINITY_TEST_USED_MPIDR, 0UL,
			    PSCI_RETURN_INVALID_PARAMS);
}

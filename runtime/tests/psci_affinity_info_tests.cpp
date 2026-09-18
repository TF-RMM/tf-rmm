/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_features.h>
#include <esr.h>
#include <exit.h>
#include <psci.h>
#include <rec.h>
}

#include "rtt_data_test_helpers.h"

/*
 * PSCI_AFFINITY_INFO for an MPIDR that identifies no REC.
 *
 * DEN0137 2.0-bet3 B6.3.1.2 target_match: if !MpidrIsUsed(realm,
 * target_affinity) the result is PSCI_INVALID_PARAMETERS, where B3.55
 * MpidrIsUsed is true only when the MPIDR identifies a REC in the Realm.
 * B6.3.1.3 not_runnable reserves PSCI_OFF for a REC that exists and is
 * not runnable. DEN0022 5.7.2 returns INVALID_PARAMETERS for an affinity
 * instance that is not present. Arm's cca-rmm-acs cmd_affinity_info
 * (target_match, MPIDR_NOT_USED) expects PSCI_E_INVALID_PARAMS.
 *
 * The tests build an RD with its auxiliary granules and an empty
 * MPIDR-to-REC map the way RMI_REALM_CREATE initialises them, register
 * one non-runnable REC for MPIDR 1, and drive handle_realm_exit() with an
 * SMC syndrome from a Plane 0 REC of that Realm (MPIDR 0), the way
 * exit_esr_tests.cpp drives it.
 */

#define AFFINITY_TEST_RTT_START_IDX	112000U
#define AFFINITY_TEST_NS_LIST_START_IDX	127000U

#define AFFINITY_TEST_SELF_MPIDR	0UL
#define AFFINITY_TEST_USED_MPIDR	1UL
#define AFFINITY_TEST_UNUSED_MPIDR	2UL
#define AFFINITY_TEST_GPR_MARKER	0xa5a5a5a5UL

#define AFFINITY_TEST_NUM_RD_AUX	\
	(unsigned int)(round_up(sizeof(struct rd_aux), GRANULE_SIZE) / \
		       GRANULE_SIZE)

struct affinity_test_context {
	STRUCT_TYPE sysreg_state sysregs[1];
	struct rec rec;
	struct rmi_rec_exit rec_exit;
};

TEST_GROUP(psci_affinity_info_tests) {
	TEST_SETUP()
	{
		static bool counters_initialized;

		if (!counters_initialized) {
			reset_data_granule_allocation();
			g_rtt_next_idx = AFFINITY_TEST_RTT_START_IDX;
			g_ns_list_next_idx = AFFINITY_TEST_NS_LIST_START_IDX;
			counters_initialized = true;
		}
		test_helpers_init();
		test_helpers_rmm_start(true);
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
	}
};

/*
 * Attach the RD auxiliary granules and initialise the object maps the way
 * rd_init_aux_granules() does during RMI_REALM_CREATE.
 */
static void add_rd_aux_granules(const struct test_data_ctx *ctx)
{
	struct granule *g_rd = tr_find_fine_granule(ctx->rd);
	uintptr_t aux_base = reserve_delegated_granules(AFFINITY_TEST_NUM_RD_AUX);
	struct rd_aux *rd_aux;
	struct sarray_hdr *hnd;
	struct rd *rd;

	granule_lock(g_rd, GRANULE_STATE_RD);
	rd = (struct rd *)buffer_granule_map(g_rd, SLOT_RD);
	CHECK_TRUE(rd != NULL);

	rd->num_rd_aux = AFFINITY_TEST_NUM_RD_AUX;
	for (unsigned int i = 0U; i < AFFINITY_TEST_NUM_RD_AUX; i++) {
		struct granule *g_aux = tr_find_fine_granule(aux_base +
						     ((uintptr_t)i * GRANULE_SIZE));

		granule_lock(g_aux, GRANULE_STATE_DELEGATED);
		granule_unlock_transition(g_aux, GRANULE_STATE_RD_AUX);
		rd->aux_granules[i] = g_aux;
	}

	rd_aux = (struct rd_aux *)buffer_rd_aux_granules_map_zeroed(
					&rd->aux_granules[0], rd->num_rd_aux);
	CHECK_TRUE(rd_aux != NULL);
	hnd = sarray_init_vdev_map(&rd_aux->vdev_map_hnd, rd_aux->vdev_map_mem,
				   sizeof(rd_aux->vdev_map_mem));
	CHECK_TRUE(hnd != NULL);
	hnd = sarray_init_rec_map(&rd_aux->mpidr_rec_map.rec_map_hnd,
				  rd_aux->mpidr_rec_map.rec_map_mem,
				  sizeof(rd_aux->mpidr_rec_map.rec_map_mem));
	CHECK_TRUE(hnd != NULL);
	buffer_rd_aux_granules_unmap(rd_aux, rd->num_rd_aux);

	buffer_unmap(rd);
	granule_unlock(g_rd);
}

/* Create a non-runnable REC granule for @mpidr and register it in the map. */
static void add_rec(const struct test_data_ctx *ctx, unsigned long mpidr)
{
	uintptr_t rec_pa = reserve_delegated_granules(1U);
	struct granule *g_rec = tr_find_fine_granule(rec_pa);
	struct granule *g_rd = tr_find_fine_granule(ctx->rd);
	struct rec_map rec_map;
	struct rd_aux *rd_aux;
	struct rec *rec;
	struct rd *rd;
	int ret;

	granule_lock(g_rec, GRANULE_STATE_DELEGATED);
	rec = (struct rec *)buffer_granule_map_zeroed(g_rec, SLOT_REC);
	CHECK_TRUE(rec != NULL);
	rec->g_rec = g_rec;
	rec->realm_info.g_rd = g_rd;
	rec->mpidr = mpidr;
	rec->runnable = false;
	buffer_unmap(rec);
	granule_unlock_transition(g_rec, GRANULE_STATE_REC);

	granule_lock(g_rd, GRANULE_STATE_RD);
	rd = (struct rd *)buffer_granule_map(g_rd, SLOT_RD);
	CHECK_TRUE(rd != NULL);
	rd_aux = (struct rd_aux *)buffer_rd_aux_granules_map(
					&rd->aux_granules[0], rd->num_rd_aux);
	CHECK_TRUE(rd_aux != NULL);

	rec_map.rec = rec_pa;
	ret = sarray_insert_rec_map(&rd_aux->mpidr_rec_map.rec_map_hnd, mpidr,
				    &rec_map);
	LONGS_EQUAL(0, ret);

	buffer_rd_aux_granules_unmap(rd_aux, rd->num_rd_aux);
	buffer_unmap(rd);
	granule_unlock(g_rd);
}

static void build_realm(struct test_data_ctx *ctx)
{
	CHECK_TRUE(create_data_realm_base(ctx));
	add_rd_aux_granules(ctx);
	add_rec(ctx, AFFINITY_TEST_USED_MPIDR);
}

/*
 * Run PSCI_AFFINITY_INFO from a Plane 0 REC (MPIDR 0) of the Realm through
 * the real exit handler and return the value the Realm reads in X0.
 */
static unsigned long run_affinity_info(struct affinity_test_context *ctx,
				       const struct test_data_ctx *realm,
				       unsigned long target_affinity,
				       unsigned long lowest_affinity_level)
{
	(void)memset(ctx, 0, sizeof(*ctx));

	ctx->rec.active_plane_id = PLANE_0_ID;
	ctx->rec.gic_owner = PLANE_0_ID;
	ctx->rec.aux_data.sysregs = &ctx->sysregs[0];
	ctx->rec.realm_info.num_aux_planes = 0U;
	ctx->rec.realm_info.primary_s2_ctx.ipa_bits = GRANULE_SHIFT + 2U;
	ctx->rec.realm_info.g_rd = tr_find_fine_granule(realm->rd);
	ctx->rec.mpidr = AFFINITY_TEST_SELF_MPIDR;

	ctx->rec.plane[0].regs[0] = SMC64_PSCI_AFFINITY_INFO;
	ctx->rec.plane[0].regs[1] = target_affinity;
	ctx->rec.plane[0].regs[2] = lowest_affinity_level;
	ctx->rec.plane[0].regs[4] = AFFINITY_TEST_GPR_MARKER;

	write_elr_el2(0x1000UL);
	write_esr_el2(ESR_EL2_EC_SMC | MASK(ESR_EL2_IL));

	CHECK_TRUE(handle_realm_exit(&ctx->rec, &ctx->rec_exit,
				     ARM_EXCEPTION_SYNC_LEL));
	UNSIGNED_LONGS_EQUAL(0x1004UL, read_elr_el2());
	UNSIGNED_LONGS_EQUAL(AFFINITY_TEST_GPR_MARKER, ctx->rec.plane[0].regs[4]);

	return ctx->rec.plane[0].regs[0];
}

/* Control: the calling REC itself is on. */
TEST(psci_affinity_info_tests, self_is_on)
{
	struct test_data_ctx realm;
	struct affinity_test_context ctx;

	build_realm(&realm);

	UNSIGNED_LONGS_EQUAL(PSCI_AFFINITY_INFO_ON,
			     run_affinity_info(&ctx, &realm,
					       AFFINITY_TEST_SELF_MPIDR, 0UL));
}

/* Control, B6.3.1.3 not_runnable: an existing REC that is off reports OFF. */
TEST(psci_affinity_info_tests, used_mpidr_not_runnable_is_off)
{
	struct test_data_ctx realm;
	struct affinity_test_context ctx;

	build_realm(&realm);

	UNSIGNED_LONGS_EQUAL(PSCI_AFFINITY_INFO_OFF,
			     run_affinity_info(&ctx, &realm,
					       AFFINITY_TEST_USED_MPIDR, 0UL));
}

/* Control, B6.3.1.2 target_bound: a non-zero affinity level is rejected. */
TEST(psci_affinity_info_tests, nonzero_affinity_level_is_invalid)
{
	struct test_data_ctx realm;
	struct affinity_test_context ctx;

	build_realm(&realm);

	UNSIGNED_LONGS_EQUAL(PSCI_RETURN_INVALID_PARAMS,
			     run_affinity_info(&ctx, &realm,
					       AFFINITY_TEST_USED_MPIDR, 1UL));
}

/* B6.3.1.2 target_match: an MPIDR with no REC is INVALID_PARAMETERS. */
TEST(psci_affinity_info_tests, unused_mpidr_is_invalid_parameters)
{
	struct test_data_ctx realm;
	struct affinity_test_context ctx;

	build_realm(&realm);

	UNSIGNED_LONGS_EQUAL(PSCI_RETURN_INVALID_PARAMS,
			     run_affinity_info(&ctx, &realm,
					       AFFINITY_TEST_UNUSED_MPIDR, 0UL));
}

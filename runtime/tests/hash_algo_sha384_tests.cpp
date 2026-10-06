/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <rec.h>
#include <rsi-handler.h>
}

#include "rtt_data_test_helpers.h"

extern "C" {
#include <smc-rsi.h>
}

/*
 * SHA-384 reporting through RMI_FEATURES and RSI_REALM_CONFIG.
 *
 * DEN0137 2.0-bet3 B3.136 RmiFeatureRegisterEncode sets
 * RmiFeatureRegister1.HASH_SHA_384 from rmm.static.feat_sha_384, the same
 * attribute that B3.113 RealmParamsSupported uses to accept or reject
 * RMI_HASH_SHA_384 in RMI_REALM_CREATE (B4.5.40.2 params_supp, RKPBQM).
 * As RMI_REALM_CREATE accepts SHA-384, the feature register must
 * advertise it.
 *
 * B5.4.16.3 hash_algo requires RSI_REALM_CONFIG to report
 * Equal(cfg.hash_algo, realm.hash_algo); RsiHashAlgorithm (B5.5.10)
 * encodes SHA-384 as 2.
 *
 * The RSI_REALM_CONFIG tests build a Realm with one DATA granule mapped
 * at TEST_DATA_IPA_BASE, point a REC at that Realm and drive the handler
 * directly, then read the configuration structure back from the DATA
 * granule the way the Realm would.
 */

struct config_test_context {
	STRUCT_TYPE sysreg_state sysregs[1];
	struct rec rec;
};

TEST_GROUP(hash_algo_sha384_tests) {
	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start(false);
		reset_data_granule_allocation();
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
	}

	TEST_TEARDOWN()
	{
	}
};

/*
 * B3.136: every hash algorithm accepted by RMI_REALM_CREATE is advertised
 * in RmiFeatureRegister1.
 */
TEST(hash_algo_sha384_tests, feature_register_1_advertises_sha384)
{
	struct smc_result res = {};

	smc_read_feature_register(RMI_FEATURE_REGISTER_1_INDEX, &res);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(RMI_FEATURE_TRUE,
			     EXTRACT(RMI_FEATURE_REGISTER_1_HASH_SHA_256,
				     res.x[1]));
	UNSIGNED_LONGS_EQUAL(RMI_FEATURE_TRUE,
			     EXTRACT(RMI_FEATURE_REGISTER_1_HASH_SHA_384,
				     res.x[1]));
	UNSIGNED_LONGS_EQUAL(RMI_FEATURE_TRUE,
			     EXTRACT(RMI_FEATURE_REGISTER_1_HASH_SHA_512,
				     res.x[1]));
}

/*
 * Run RSI_REALM_CONFIG for a REC of a Realm whose hash algorithm is
 * @algorithm and return the algorithm value written to the Realm's page.
 */
static unsigned char run_realm_config(struct config_test_context *ctx,
				      enum hash_algo algorithm)
{
	struct test_data_ctx data;
	struct rsi_result res;
	struct rsi_realm_config *config;
	struct granule *g_rd;
	struct rd *rd;
	uintptr_t data_pa;

	CHECK_TRUE(create_data_rtt_ctx(&data));
	CHECK_TRUE(init_ripas_range(&data, TEST_DATA_IPA_BASE,
				    TEST_DATA_PAGE_TOP));
	data_pa = reserve_delegated_granules(1U);
	CHECK_TRUE(map_data_page(&data, TEST_DATA_IPA_BASE, data_pa));

	(void)memset(ctx, 0, sizeof(*ctx));
	ctx->rec.active_plane_id = PLANE_0_ID;
	ctx->rec.gic_owner = PLANE_0_ID;
	ctx->rec.aux_data.sysregs = &ctx->sysregs[0];
	ctx->rec.realm_info.num_aux_planes = 0U;
	ctx->rec.realm_info.algorithm = algorithm;

	g_rd = tr_find_fine_granule(data.rd);
	CHECK_TRUE(g_rd != NULL);
	granule_lock(g_rd, GRANULE_STATE_RD);
	rd = (struct rd *)buffer_granule_map(g_rd, SLOT_RD);
	CHECK_TRUE(rd != NULL);
	ctx->rec.realm_info.primary_s2_ctx = rd->s2_ctx[PRIMARY_S2_CTX_ID];
	buffer_unmap(rd);
	granule_unlock(g_rd);
	ctx->rec.realm_info.g_rd = g_rd;

	/* Seed the page so an untouched field is detected. */
	config = (struct rsi_realm_config *)data_pa;
	config->algorithm = 0xa5U;

	ctx->rec.plane[0].regs[1] = TEST_DATA_IPA_BASE;
	(void)memset(&res, 0, sizeof(res));

	handle_rsi_realm_config(&ctx->rec, &res);

	UNSIGNED_LONGS_EQUAL(RSI_SUCCESS, res.smc_res.x[0]);
	UNSIGNED_LONGS_EQUAL(TEST_IPA_BITS, config->ipa_width);

	return config->algorithm;
}

/* Controls: the two algorithms the handler already distinguished. */
TEST(hash_algo_sha384_tests, realm_config_reports_sha256)
{
	struct config_test_context ctx;

	UNSIGNED_LONGS_EQUAL(RSI_HASH_SHA_256,
			     run_realm_config(&ctx, HASH_SHA_256));
}

TEST(hash_algo_sha384_tests, realm_config_reports_sha512)
{
	struct config_test_context ctx;

	UNSIGNED_LONGS_EQUAL(RSI_HASH_SHA_512,
			     run_realm_config(&ctx, HASH_SHA_512));
}

/* B5.4.16.3 hash_algo: a SHA-384 Realm reads back RSI_HASH_SHA_384. */
TEST(hash_algo_sha384_tests, realm_config_reports_sha384)
{
	struct config_test_context ctx;

	UNSIGNED_LONGS_EQUAL(RSI_HASH_SHA_384,
			     run_realm_config(&ctx, HASH_SHA_384));
}

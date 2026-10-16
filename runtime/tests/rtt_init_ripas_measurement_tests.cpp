/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

#include "rtt_data_test_helpers.h"

#define INIT_RIPAS_MEASURE_TOP	(TEST_DATA_IPA_BASE + 4UL * GRANULE_SIZE)

/*
 * Known digests generated independently with Python hashlib. The input is a
 * zeroed 0x100-byte RmmMeasurementDescriptorRipas, with desc_type=2, len=0x100,
 * the previous digest at offset 0x10, and little-endian base/top at 0x50/0x58.
 * The initial digest contains bytes 1 through the hash size, zero padded to
 * 64 bytes. Each successful command measures [base, out_top) exactly once.
 */
static const unsigned char sha256_range_rim[MAX_MEASUREMENT_SIZE] = {
	0x5b, 0x25, 0x62, 0xae, 0x01, 0xd0, 0x01, 0x70,
	0x8d, 0x60, 0x66, 0x57, 0xe9, 0x52, 0x12, 0x83,
	0x1a, 0xbe, 0xbd, 0x9b, 0x6c, 0xd0, 0x9d, 0x77,
	0xd0, 0x45, 0xd1, 0xfe, 0x6b, 0xf3, 0x30, 0xae
};

static const unsigned char sha256_partial_rim[MAX_MEASUREMENT_SIZE] = {
	0xd3, 0x4a, 0xd2, 0xdb, 0xd1, 0x8e, 0xaa, 0xb8,
	0x6c, 0x83, 0xc8, 0xfa, 0xff, 0x69, 0xfd, 0x32,
	0xd0, 0x06, 0x0b, 0xc1, 0xba, 0x9a, 0xe5, 0x84,
	0x8b, 0xb8, 0x74, 0x22, 0xa0, 0x42, 0xa8, 0x38
};

static const unsigned char sha384_range_rim[MAX_MEASUREMENT_SIZE] = {
	0x7b, 0xed, 0x25, 0xfe, 0xe3, 0x78, 0xd4, 0xcb,
	0x95, 0xf4, 0xb7, 0x55, 0x23, 0xdf, 0x6c, 0x70,
	0xf2, 0x7e, 0x9e, 0x26, 0xde, 0x14, 0x19, 0x01,
	0x4e, 0x95, 0xb9, 0x06, 0x70, 0xce, 0xf3, 0x89,
	0xf7, 0xb7, 0x8e, 0xba, 0xab, 0x35, 0xef, 0x91,
	0xe7, 0x1a, 0xcd, 0x62, 0xbc, 0xd6, 0x10, 0x0d
};

static const unsigned char sha512_range_rim[MAX_MEASUREMENT_SIZE] = {
	0xa9, 0x7a, 0xb9, 0x1d, 0xcb, 0xd5, 0x94, 0xec,
	0xca, 0xdf, 0xd2, 0xf7, 0x21, 0xaf, 0x2e, 0x2f,
	0x22, 0xdb, 0x4a, 0x88, 0xc4, 0xe9, 0xdc, 0xde,
	0x4f, 0xdf, 0x0b, 0xc9, 0xdf, 0x3d, 0x99, 0x4e,
	0xbc, 0x63, 0x2c, 0xde, 0x6a, 0xe4, 0x3c, 0x0d,
	0xdc, 0xa2, 0x44, 0x6c, 0x9f, 0x54, 0x25, 0x5c,
	0x99, 0x20, 0x65, 0xbf, 0x6e, 0x37, 0x4c, 0x18,
	0xf2, 0xd5, 0x97, 0xa1, 0x95, 0x4f, 0x6a, 0xec
};

TEST_GROUP(rtt_init_ripas_measurement_tests) {
	struct test_data_ctx ctx;
	unsigned char initial_rim[MAX_MEASUREMENT_SIZE];

	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start(false);
		reset_data_granule_allocation();
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
	}
};

static void prepare(struct test_data_ctx *ctx, unsigned char initial_rim[],
		    enum hash_algo algorithm)
{
	struct rmi_test_realm realm;
	struct rmi_realm_params *params;
	struct granule *g_rd;
	struct rd *rd;

	rmi_test_realm_prepare(&realm, allocate_rtt_granules);
	params = (struct rmi_realm_params *)realm.params;
	params->s2sz = TEST_IPA_BITS;
	params->algorithm = (unsigned char)algorithm;
	rmi_test_realm_create(&realm);
	ctx->rd = realm.rd;
	ctx->rtt_l0 = realm.rtt;
	CHECK_TRUE(create_data_rtts(ctx));

	(void)memset(initial_rim, 0, MAX_MEASUREMENT_SIZE);
	for (size_t i = 0U; i < measurement_get_size(algorithm); i++) {
		initial_rim[i] = (unsigned char)(i + 1U);
	}
	g_rd = tr_find_fine_granule(ctx->rd);
	granule_lock(g_rd, GRANULE_STATE_RD);
	rd = (struct rd *)buffer_granule_map(g_rd, SLOT_RD);
	(void)memcpy(rd->measurement[RIM_MEASUREMENT_SLOT], initial_rim,
		     MAX_MEASUREMENT_SIZE);
	buffer_unmap(rd);
	granule_unlock(g_rd);
}

static void expect_rim(const struct test_data_ctx *ctx,
		       const unsigned char *expected)
{
	struct granule *g_rd = tr_find_fine_granule(ctx->rd);
	struct rd *rd;
	unsigned char actual[MAX_MEASUREMENT_SIZE];

	granule_lock(g_rd, GRANULE_STATE_RD);
	rd = (struct rd *)buffer_granule_map(g_rd, SLOT_RD);
	(void)memcpy(actual, rd->measurement[RIM_MEASUREMENT_SLOT],
		     sizeof(actual));
	buffer_unmap(rd);
	granule_unlock(g_rd);
	MEMCMP_EQUAL(expected, actual, sizeof(actual));
}

static void init_range(const struct test_data_ctx *ctx, unsigned long base,
		       unsigned long top, unsigned long out_top)
{
	struct smc_result res = {};

	smc_rtt_init_ripas(ctx->rd, base, top, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(out_top, res.x[1]);
}

/* Model the marker held by an unfinished map/unmap, without creating an SRO. */
static unsigned long install_pending_entry(const struct test_data_ctx *ctx,
					  unsigned long ipa, enum ripas ripas)
{
	struct s2tt_context s2_ctx;
	struct s2tt_walk wi;
	unsigned long *table;
	unsigned long s2tte;

	init_data_s2_ctx(ctx, &s2_ctx);
	granule_lock(s2_ctx.g_rtt, GRANULE_STATE_RTT);
	s2tt_walk_lock_unlock(&s2_ctx, ipa, S2TT_PAGE_LEVEL, &wi);
	table = (unsigned long *)buffer_granule_mecid_map(wi.g_llt, SLOT_RTT,
							  s2_ctx.mecid);
	s2tte = s2tte_read(&table[wi.index]);
	if (ripas == RIPAS_EMPTY) {
		s2tte = s2tte_create_unassigned_empty(&s2_ctx, s2tte);
	} else if (ripas == RIPAS_RAM) {
		s2tte = s2tte_create_unassigned_ram(&s2_ctx, s2tte);
	} else {
		s2tte = s2tte_create_unassigned_destroyed(&s2_ctx, s2tte);
	}
	s2tte = s2tte_set_drain_pending(s2tte, 17U);
	if (ripas == RIPAS_DESTROYED) {
		s2tte = s2tte_set_tlbi_pending(s2tte);
	}
	s2tte_write(&table[wi.index], s2tte);
	buffer_unmap(table);
	granule_unlock(wi.g_llt);
	return s2tte;
}

TEST(rtt_init_ripas_measurement_tests, sha256_measures_multi_page_range_once)
{
	prepare(&ctx, initial_rim, HASH_SHA_256);
	init_range(&ctx, TEST_DATA_IPA_BASE, INIT_RIPAS_MEASURE_TOP,
		   INIT_RIPAS_MEASURE_TOP);
	expect_rim(&ctx, sha256_range_rim);
}

TEST(rtt_init_ripas_measurement_tests, sha384_measures_multi_page_range_once)
{
	prepare(&ctx, initial_rim, HASH_SHA_384);
	init_range(&ctx, TEST_DATA_IPA_BASE, INIT_RIPAS_MEASURE_TOP,
		   INIT_RIPAS_MEASURE_TOP);
	expect_rim(&ctx, sha384_range_rim);
}

TEST(rtt_init_ripas_measurement_tests, sha512_measures_multi_page_range_once)
{
	prepare(&ctx, initial_rim, HASH_SHA_512);
	init_range(&ctx, TEST_DATA_IPA_BASE, INIT_RIPAS_MEASURE_TOP,
		   INIT_RIPAS_MEASURE_TOP);
	expect_rim(&ctx, sha512_range_rim);
}

TEST(rtt_init_ripas_measurement_tests, already_ram_extends_previous_rim)
{
	static const unsigned char expected[MAX_MEASUREMENT_SIZE] = {
		0xa3, 0x7a, 0x4b, 0x86, 0xfa, 0xa4, 0x13, 0x78,
		0x0e, 0x80, 0x69, 0x10, 0xa8, 0x9c, 0xe7, 0x99,
		0xd5, 0x6d, 0x60, 0x85, 0xdb, 0x9d, 0x29, 0x98,
		0x51, 0x7b, 0x61, 0xb2, 0xf4, 0x73, 0xb6, 0x47
	};

	prepare(&ctx, initial_rim, HASH_SHA_256);
	init_range(&ctx, TEST_DATA_IPA_BASE, INIT_RIPAS_MEASURE_TOP,
		   INIT_RIPAS_MEASURE_TOP);
	expect_rim(&ctx, sha256_range_rim);
	init_range(&ctx, TEST_DATA_IPA_BASE, INIT_RIPAS_MEASURE_TOP,
		   INIT_RIPAS_MEASURE_TOP);
	expect_rim(&ctx, expected);
}

TEST(rtt_init_ripas_measurement_tests, device_limits_measured_range_to_out_top)
{
	unsigned long stop = TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE;
	uintptr_t dev_pa;

	prepare(&ctx, initial_rim, HASH_SHA_256);
	dev_pa = reserve_delegated_granules(1U);
	CHECK_TRUE(install_assigned_dev_mapping(&ctx, stop, dev_pa,
					      S2TT_PAGE_LEVEL));
	init_range(&ctx, TEST_DATA_IPA_BASE, INIT_RIPAS_MEASURE_TOP, stop);
	expect_rim(&ctx, sha256_partial_rim);
}

TEST(rtt_init_ripas_measurement_tests, pending_first_entry_preserves_rim)
{
	const enum ripas states[] = { RIPAS_EMPTY, RIPAS_RAM, RIPAS_DESTROYED };

	for (unsigned int i = 0U; i < ARRAY_SIZE(states); i++) {
		struct smc_result res = {};
		unsigned long pending;

		prepare(&ctx, initial_rim, HASH_SHA_256);
		pending = install_pending_entry(&ctx, TEST_DATA_IPA_BASE, states[i]);
		smc_rtt_init_ripas(ctx.rd, TEST_DATA_IPA_BASE,
				   INIT_RIPAS_MEASURE_TOP, &res);
		UNSIGNED_LONGS_EQUAL(RMI_BLOCKED, res.x[0]);
		UNSIGNED_LONGS_EQUAL(pending,
			read_data_ipa_raw_s2tte(&ctx, TEST_DATA_IPA_BASE));
		expect_rim(&ctx, initial_rim);
	}
}

TEST(rtt_init_ripas_measurement_tests, pending_entry_limits_measured_range)
{
	const enum ripas states[] = { RIPAS_EMPTY, RIPAS_RAM, RIPAS_DESTROYED };
	unsigned long stop = TEST_DATA_IPA_BASE + 2UL * GRANULE_SIZE;

	for (unsigned int i = 0U; i < ARRAY_SIZE(states); i++) {
		unsigned long pending;

		prepare(&ctx, initial_rim, HASH_SHA_256);
		pending = install_pending_entry(&ctx, stop, states[i]);
		init_range(&ctx, TEST_DATA_IPA_BASE, INIT_RIPAS_MEASURE_TOP, stop);
		UNSIGNED_LONGS_EQUAL(pending, read_data_ipa_raw_s2tte(&ctx, stop));
		expect_rim(&ctx, sha256_partial_rim);
	}
}

TEST(rtt_init_ripas_measurement_tests, table_boundary_limits_measured_range)
{
	static const unsigned char expected[MAX_MEASUREMENT_SIZE] = {
		0x3c, 0x71, 0x5f, 0x70, 0x29, 0xe8, 0xe7, 0x04,
		0x19, 0x7a, 0x3d, 0x73, 0x08, 0x60, 0x3c, 0xc8,
		0x89, 0xab, 0xa9, 0x31, 0xe3, 0x6c, 0x3f, 0x73,
		0xaf, 0xd2, 0x84, 0xc4, 0x00, 0xb8, 0xc5, 0x2c
	};

	prepare(&ctx, initial_rim, HASH_SHA_256);
	init_range(&ctx, TEST_DATA_L2_BLOCK_TOP - GRANULE_SIZE,
		   TEST_DATA_L2_BLOCK_TOP + GRANULE_SIZE,
		   TEST_DATA_L2_BLOCK_TOP);
	expect_rim(&ctx, expected);
}

TEST(rtt_init_ripas_measurement_tests, measures_block_range)
{
	static const unsigned char expected[MAX_MEASUREMENT_SIZE] = {
		0xe1, 0xbe, 0x5a, 0x0f, 0xc7, 0x46, 0x39, 0xb1,
		0x5d, 0x26, 0xe8, 0xae, 0x13, 0x5c, 0x3c, 0x76,
		0xf1, 0x45, 0x64, 0xaf, 0x01, 0x71, 0x31, 0x84,
		0x84, 0x54, 0x34, 0x3f, 0x45, 0x63, 0xd8, 0xdc
	};
	unsigned long top = TEST_DATA_L2_BLOCK_TOP + TEST_DATA_L2_BLOCK_SIZE;

	prepare(&ctx, initial_rim, HASH_SHA_256);
	init_range(&ctx, TEST_DATA_L2_BLOCK_TOP, top, top);
	expect_rim(&ctx, expected);
}

TEST(rtt_init_ripas_measurement_tests, incompatible_first_entry_preserves_rim)
{
	struct smc_result res = {};
	uintptr_t dev_pa;

	prepare(&ctx, initial_rim, HASH_SHA_256);
	dev_pa = reserve_delegated_granules(1U);
	CHECK_TRUE(install_assigned_dev_mapping(&ctx, TEST_DATA_IPA_BASE, dev_pa,
					      S2TT_PAGE_LEVEL));
	smc_rtt_init_ripas(ctx.rd, TEST_DATA_IPA_BASE, INIT_RIPAS_MEASURE_TOP,
			   &res);
	UNSIGNED_LONGS_EQUAL(pack_return_code_level(RMI_ERROR_RTT, S2TT_PAGE_LEVEL),
			     res.x[0]);
	expect_rim(&ctx, initial_rim);
}

TEST(rtt_init_ripas_measurement_tests, unaligned_block_base_preserves_rim)
{
	struct smc_result res = {};
	unsigned long base = TEST_DATA_L2_BLOCK_TOP + GRANULE_SIZE;

	prepare(&ctx, initial_rim, HASH_SHA_256);
	smc_rtt_init_ripas(ctx.rd, base, base + GRANULE_SIZE, &res);
	UNSIGNED_LONGS_EQUAL(pack_return_code_level(RMI_ERROR_RTT, 2U), res.x[0]);
	expect_rim(&ctx, initial_rim);
}

TEST(rtt_init_ripas_measurement_tests, top_inside_first_block_preserves_rim)
{
	struct smc_result res = {};

	prepare(&ctx, initial_rim, HASH_SHA_256);
	smc_rtt_init_ripas(ctx.rd, TEST_DATA_L2_BLOCK_TOP,
			   TEST_DATA_L2_BLOCK_TOP + GRANULE_SIZE, &res);
	UNSIGNED_LONGS_EQUAL(pack_return_code_level(RMI_ERROR_RTT, 2U), res.x[0]);
	expect_rim(&ctx, initial_rim);
}

TEST(rtt_init_ripas_measurement_tests, empty_range_preserves_rim)
{
	struct smc_result res = {};

	prepare(&ctx, initial_rim, HASH_SHA_256);
	smc_rtt_init_ripas(ctx.rd, TEST_DATA_IPA_BASE, TEST_DATA_IPA_BASE, &res);
	UNSIGNED_LONGS_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	expect_rim(&ctx, initial_rim);
}

TEST(rtt_init_ripas_measurement_tests, active_realm_preserves_rim)
{
	struct smc_result res = {};

	prepare(&ctx, initial_rim, HASH_SHA_256);
	smc_realm_activate(ctx.rd, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	smc_rtt_init_ripas(ctx.rd, TEST_DATA_IPA_BASE, INIT_RIPAS_MEASURE_TOP,
			   &res);
	UNSIGNED_LONGS_EQUAL(RMI_ERROR_REALM, res.x[0]);
	expect_rim(&ctx, initial_rim);
}

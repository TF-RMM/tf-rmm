/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/TestHarness.h>

extern "C" {
#include <host_utils.h>
#include <measurement.h>
#include <string.h>
#include <test_helpers.h>
}

/*
 * DEN0137 2.0-bet3 B3.122: independently generated Python hashlib vectors for
 * old_REM[64] || contribution[0:size] || zeroes[64-size]. The old REM contains
 * bytes 1 through the digest length, then zeroes. The contribution contains
 * bytes 0x80 through 0xbf, including nonzero bytes beyond the requested size.
 * Chained vectors extend the initial REM with sizes 1, 0, 63, then 64, padding
 * each intermediate digest to 64 bytes before the next extend.
 */
static const size_t contribution_sizes[] = {0U, 1U, 31U, 32U, 47U, 48U, 63U, 64U};

static const char *const sha256_expected[] = {
	"95b9b0ff914c2c1987c21ff86ed616cac6c58b9ddcd21ee800c8a89ff220d5d1",
	"4c83fc3e8bdb99c21d65ec9fe8f8578ced7ef9c891d9537bd587832c2ac18b0e",
	"4a86e7d430f834fbb615cd5eece3e0ec385ed6d3f5b7c66b767fe12417f79bc4",
	"267b4f54eead4081a0feecd8a015fa6e376e9c32e8ca7a1993ad5dbebea7b33d",
	"a06ae7e43ad31f82d6b84800365e763f8cd6ba9de20bf1d728bcd6cada5b79e7",
	"8291320f20aca175d70b90c61abb89ac9544c500ea7bb8a827f94afe3c31b403",
	"e3cd162979fd3564937c097d09139fae19606c0794cfe65471b2b0789c037d82",
	"aa5474e8ca98af484d107a5a1c78e3d5fddae5f460f411571ad97cbae9899692",
};

static const char *const sha384_expected[] = {
	"dd974568df8d5b6fb24f42faec865b2c9d3709253701ad6622859a4d689dd95878d475b633ab78142c8e5fd9a1591e15",
	"dbe7357ee884f509e126e6d91ea1697dbbfa3ad65fee19b8ee1b6115d0c830f2003cf1ff97b40952863af8a586ff3dd1",
	"bc4f959c14080bdc5d79a4e5098076684f9b0a6f01f598161637b009ea08747e5070415f69ffc4a012bb3ad91b2ec9ba",
	"f775f53638285bb6e2e252ba7f45fb14223f02b67d3f97e987077cc6add4a27a29eb45743436c8bf2446f4c403bf98ae",
	"e18e6b38ac873706e7d6af29a525813b0c7f115a09ab4d31bc73bd8ab1a60a759e6b1fe8bac7c0a670c559be9d64e4c1",
	"2a7e5535523bfbc5797fd7b276d048b27e849a00f39b623f0f52f9652c576ff0362df48a22a2c2877a890cfbf55df638",
	"1f9baf742f4cfde0798b05cbd9369a284c673e25e833fddec1c8f5755a7a6e0639db9dfcb174fd4bbae6f9665e077f64",
	"60efc08700915198604c038cc150a3a41923556140e90167df1d03135c17bc46a29e6457be6b885529a948daecb41172",
};

static const char *const sha512_expected[] = {
	"f56fff19a38a0272b32a166a47a8696d821e020f92c1d47bedb792bddc91941465dd0b63b63b03e1ea84862c195389e5fde631463c74ac25d114874de364e0cf",
	"f38ff90fd328fd1677fc1cd91d685a79a9cd6cdefa5523a7b03f3bc1331dc977e5bbfd2bd9107402251ff17f59be9161ec4dcbea84d4f5d2fa2219ac4f1faa93",
	"f669ba162d396a6f25188e162fb0cbbd660946d99a0c1850906e9a2a97e185605b92613e5845f66249978017349b5487926da7b58aca1e2527a0f065b479fc83",
	"e24fd3e8ea8ff03d8a76ef47652c6b68ea018bccb7ecbdade1e29e86617f70ad873a9731029b734deaa1c6f66be469cb5906fb92d718ede7c6cb807570e78f34",
	"50902dd332a32a93b5c53a5927ee087f37cd7dd59dfa7f89047f76b3be9842fedfd11c7bb1ab9b86c141e1c8f88cd313116162f3bb3c3bdaefdd0fad5ecc1d26",
	"94349f2ef554d9d30f25124d780a023af52b55896a55d53f0056bf20b09d3fb157cfe78f8a9f85defb96a9be709ac3513770bfe719f220201bdf2daf0f6979fb",
	"d1051b0f478583b02041f28437b3f8a86de26210b256dc8ef34ef42c0f019ee33c1b98952750c83e8296bbb5d39e0aa419b6465e440be923386f73e483287828",
	"1f7e016003524db043c84f86c9d09555b98ce3c935c174ebacc3b405a963264f1570d9d8bb7b9209c8ed565261c5ab4adbfd65e7252719a31a142ae5c3d7f770",
};

TEST_GROUP(measurement_extend_tests) {
	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start(false);
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
	}
};

static void init_measurement(unsigned char *measurement,
			     unsigned char *contribution, size_t hash_size)
{
	(void)memset(measurement, 0, MAX_MEASUREMENT_SIZE);
	for (size_t i = 0U; i < hash_size; i++) {
		measurement[i] = (unsigned char)(i + 1U);
	}
	for (size_t i = 0U; i < MAX_MEASUREMENT_SIZE; i++) {
		contribution[i] = (unsigned char)(0x80U + i);
	}
}

static void expect_measurement(const unsigned char *measurement,
			       const char *expected, size_t hash_size)
{
	static const char digits[] = "0123456789abcdef";
	char hex[2U * MAX_MEASUREMENT_SIZE + 1U];

	for (size_t i = 0U; i < hash_size; i++) {
		hex[2U * i] = digits[measurement[i] >> 4U];
		hex[2U * i + 1U] = digits[measurement[i] & 0xfU];
	}
	hex[2U * hash_size] = '\0';
	STRCMP_EQUAL(expected, hex);
	for (size_t i = hash_size; i < MAX_MEASUREMENT_SIZE; i++) {
		BYTES_EQUAL(0U, measurement[i]);
	}
}

static void check_vectors(enum hash_algo algorithm, const char *const *expected)
{
	unsigned char measurement[MAX_MEASUREMENT_SIZE];
	unsigned char contribution[MAX_MEASUREMENT_SIZE];
	size_t hash_size = measurement_get_size(algorithm);

	for (size_t i = 0U; i < ARRAY_SIZE(contribution_sizes); i++) {
		init_measurement(measurement, contribution, hash_size);
		measurement_extend(NULL, algorithm, measurement, contribution,
				   contribution_sizes[i], measurement,
				   sizeof(measurement));
		expect_measurement(measurement, expected[i], hash_size);
	}
}

static void check_chained(enum hash_algo algorithm, const char *expected)
{
	unsigned char measurement[MAX_MEASUREMENT_SIZE];
	unsigned char contribution[MAX_MEASUREMENT_SIZE];
	const size_t sizes[] = {1U, 0U, 63U, 64U};
	size_t hash_size = measurement_get_size(algorithm);

	init_measurement(measurement, contribution, hash_size);
	for (size_t size : sizes) {
		measurement_extend(NULL, algorithm, measurement, contribution,
				   size, measurement, sizeof(measurement));
	}
	expect_measurement(measurement, expected, hash_size);
}

TEST(measurement_extend_tests, sha256_fixed_input)
{
	check_vectors(HASH_SHA_256, sha256_expected);
}

TEST(measurement_extend_tests, sha384_fixed_input)
{
	check_vectors(HASH_SHA_384, sha384_expected);
}

TEST(measurement_extend_tests, sha512_fixed_input)
{
	check_vectors(HASH_SHA_512, sha512_expected);
}

TEST(measurement_extend_tests, sha256_chained_extends)
{
	check_chained(HASH_SHA_256,
		"6a6962c3e9079733d89cc3693dbb1ec7dc540ec04de4b404a4da21b7bb07fafd");
}

TEST(measurement_extend_tests, sha384_chained_extends)
{
	check_chained(HASH_SHA_384,
		"d04b019e916c9d80016ab63c6117ec23fb52c8a12fdbf49f8baf8e49af5a54226af10c41af26d2ef76f4767fb2ffbd50");
}

TEST(measurement_extend_tests, sha512_chained_extends)
{
	check_chained(HASH_SHA_512,
		"75c00ce25b5a9b3d02d1b0df3d79550a91bc44eb89bb0057ef06c2ad35000b88cbf2d593f5a93eeccc3db8f7c0a374d983d13315a29edd306c06d0fe1f5ec812");
}

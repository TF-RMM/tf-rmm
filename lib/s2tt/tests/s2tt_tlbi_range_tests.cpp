/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <sizes.h>
#include <s2tt_pvt_defs.h>
}

static void check_full_coverage(unsigned long total)
{
	unsigned long remaining = total;

	while (remaining != 0UL) {
		unsigned long num;
		unsigned long covered;
		unsigned int scale;

		covered = calc_s2_tlbi_range(remaining, &scale, &num);
		if (covered == 0UL) {
			UNSIGNED_LONGS_EQUAL(1UL, remaining);
			covered = 1UL;
		} else {
			CHECK_TRUE(scale <= S2_TLBI_RANGE_SCALE_MAX);
			CHECK_TRUE(num >= 1UL);
			CHECK_TRUE(num <= S2_TLBI_RANGE_NUM_MAX);
			UNSIGNED_LONGS_EQUAL(
				num << ((S2_TLBI_RANGE_SCALE_MULT * scale) +
					S2_TLBI_RANGE_SCALE_BIAS),
				covered);
		}

		CHECK_TRUE(covered <= remaining);
		remaining -= covered;
	}
}

TEST_GROUP(s2tt_tlbi_range)
{
};

TEST(s2tt_tlbi_range, single_granule_uses_non_range_tlbi)
{
	unsigned long num;
	unsigned int scale;

	UNSIGNED_LONGS_EQUAL(0UL, calc_s2_tlbi_range(1UL, &scale, &num));
	UNSIGNED_LONGS_EQUAL(0UL, num);
}

TEST(s2tt_tlbi_range, known_encodings)
{
	unsigned long num;
	unsigned long covered;
	unsigned int scale;

	covered = calc_s2_tlbi_range(2UL, &scale, &num);
	UNSIGNED_LONGS_EQUAL(2UL, covered);
	UNSIGNED_LONGS_EQUAL(0U, scale);
	UNSIGNED_LONGS_EQUAL(1UL, num);

	covered = calc_s2_tlbi_range(63UL, &scale, &num);
	UNSIGNED_LONGS_EQUAL(62UL, covered);
	UNSIGNED_LONGS_EQUAL(0U, scale);
	UNSIGNED_LONGS_EQUAL(31UL, num);

	covered = calc_s2_tlbi_range(64UL, &scale, &num);
	UNSIGNED_LONGS_EQUAL(64UL, covered);
	UNSIGNED_LONGS_EQUAL(1U, scale);
	UNSIGNED_LONGS_EQUAL(1UL, num);

	covered = calc_s2_tlbi_range(S2TTES_PER_S2TT, &scale, &num);
	UNSIGNED_LONGS_EQUAL(S2TTES_PER_S2TT, covered);
	UNSIGNED_LONGS_EQUAL(1U, scale);
	UNSIGNED_LONGS_EQUAL(8UL, num);
}

TEST(s2tt_tlbi_range, maximum_single_instruction_range)
{
	unsigned long num;
	unsigned long covered;
	unsigned int scale;
	unsigned long max_covered = S2_TLBI_RANGE_NUM_MAX <<
		((S2_TLBI_RANGE_SCALE_MULT * S2_TLBI_RANGE_SCALE_MAX) +
		 S2_TLBI_RANGE_SCALE_BIAS);

	covered = calc_s2_tlbi_range(max_covered, &scale, &num);
	UNSIGNED_LONGS_EQUAL(max_covered, covered);
	UNSIGNED_LONGS_EQUAL(S2_TLBI_RANGE_SCALE_MAX, scale);
	UNSIGNED_LONGS_EQUAL(S2_TLBI_RANGE_NUM_MAX, num);
}

TEST(s2tt_tlbi_range, complete_coverage)
{
	static const unsigned long totals[] = {
		1UL, 2UL, 3UL, 63UL, 64UL, 65UL,
		511UL, SZ_2M / GRANULE_SIZE, 513UL, 4096UL,
		SZ_1G / GRANULE_SIZE,
		(S2_TLBI_RANGE_NUM_MAX <<
		 ((S2_TLBI_RANGE_SCALE_MULT * S2_TLBI_RANGE_SCALE_MAX) +
		  S2_TLBI_RANGE_SCALE_BIAS)) + 1UL
	};

	for (unsigned long total = 1UL; total <= 4096UL; total++) {
		check_full_coverage(total);
	}

	for (unsigned int i = 0U; i < ARRAY_SIZE(totals); i++) {
		check_full_coverage(totals[i]);
	}
}

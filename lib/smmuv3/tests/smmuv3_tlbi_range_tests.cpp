/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 * Unit tests for the SMMUv3 calc_tlbi_range() helper.
 *
 * The SMMUv3 architecture defines CMD_TLBI_S2_IPA range invalidation with:
 *
 *   Range = ((NUM + 1) * 2^SCALE) * GRANULE_SIZE
 *
 * where:
 *   - NUM   is a 5-bit field (0-31), encoded as (num - 1) in the command.
 *   - SCALE is a 5-bit field without FEAT_DS (max value 31), or a 6-bit field
 *           with FEAT_DS (max value 63, values > 39 treated as 39).
 *
 * calc_tlbi_range() computes one iteration of (SCALE, NUM) such that
 * the granules covered by a single command equals (num << scale) and
 * never exceeds the remaining num_grans.
 *
 * The range-calculation tests check:
 *   1. Specific known SCALE/NUM values for well-defined inputs.
 *   2. The spec formula: covered = (NUM + 1) * 2^SCALE = num * 2^scale.
 *   3. Progress invariant: covered > 0 for every call.
 *   4. Non-overshoot invariant: covered <= num_grans.
 *   5. NUM field validity: (num - 1) fits in NUM_WIDTH bits (num <= 32).
 *   6. SCALE field validity: scale <= scale_max.
 *   7. Coverage completeness: iterating until num_grans == 0 covers the
 *      original total exactly.
 *   8. Scale clamping correctness for both scale_max=31 (no FEAT_DS) and
 *      scale_max=39 (FEAT_DS).
 */

#include <CppUTest/TestHarness.h>

extern "C" {
#include <debug.h>
#include <smc-rmi.h>
#include <smmuv3_priv.h>
}

/* Architectural constants referenced throughout the tests */
#define SCALE_MAX_NO_DS		(31U)
#define SCALE_MAX_FEAT_DS	(39U)
#define NUM_FIELD_MAX		(1UL << NUM_WIDTH)  /* max raw count = 32 */

/*
 * Helper: simulate the full invalidation loop for @num_grans_total and verify:
 *   - total covered == num_grans_total (completeness)
 *   - each iteration makes forward progress (covered > 0)
 *   - each iteration does not overshoot (covered <= remaining)
 *   - per-iteration SCALE <= scale_max
 *   - per-iteration num <= NUM_FIELD_MAX
 */
static void check_full_coverage(unsigned long num_grans_total,
				unsigned int scale_max)
{
	unsigned long remaining = num_grans_total;
	unsigned long total_covered = 0UL;

	while (remaining != 0UL) {
		unsigned int scale;
		unsigned long num, covered;

		covered = calc_tlbi_range(remaining, scale_max, &scale, &num);

		/* Forward progress */
		CHECK_TRUE(covered > 0UL);

		/* Non-overshoot */
		CHECK_TRUE(covered <= remaining);

		/* SCALE within architectural limit */
		CHECK_TRUE(scale <= scale_max);

		/* NUM + 1 fits in NUM_WIDTH bits */
		CHECK_TRUE(num >= 1UL);
		CHECK_TRUE(num <= NUM_FIELD_MAX);

		/* Spec formula: covered = (NUM + 1) * 2^SCALE = num * 2^scale */
		UNSIGNED_LONGS_EQUAL(num << scale, covered);

		total_covered += covered;
		remaining -= covered;
	}

	UNSIGNED_LONGS_EQUAL(num_grans_total, total_covered);
}

/* Exercise range calculations independently of SMMU command processing. */
TEST_GROUP(smmuv3_tlbi_range)
{
};

/*
 * TC1: Single granule -- the minimal possible input.
 *
 * Public APIs tested:
 *   calc_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify the smallest request makes progress with legal raw count and
 *   scale.
 *
 * Method:
 *   Call the helper once for one granule with the no-FEAT_DS scale limit.
 *
 * Expected results:
 *   Scale is zero, raw num is one and coverage is one granule.
 *
 * Encoding details:
 *
 *   num_grans = 1 = 0b1
 *   largest meaningful scale = floor_log2(1) = 0
 *   num = 1 >> 0 = 1
 *   covered = 1 * 2^0 = 1
 *
 *   Spec: Range = (NUM + 1) * 2^SCALE = (0 + 1) * 1 = 1 granule
 *   This checks that the smallest request makes progress with valid fields.
 */
TEST(smmuv3_tlbi_range, single_granule)
{
	unsigned int scale;
	unsigned long num, covered;

	covered = calc_tlbi_range(1UL, SCALE_MAX_NO_DS, &scale, &num);

	UNSIGNED_LONGS_EQUAL(0U, scale);
	UNSIGNED_LONGS_EQUAL(1UL, num);
	UNSIGNED_LONGS_EQUAL(1UL, covered);
}

/*
 * TC2: Cover powers of two with one command.
 *
 * Public APIs tested:
 *   calc_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify exact one-command coverage and the largest-scale tie break for
 *   powers of two.
 *
 * Method:
 *   Sweep exponents 1 through 39, selecting scale limit 31 up to exponent 31
 *   and limit 39 thereafter.
 *
 * Expected results:
 *   Each result has scale equal to the exponent, raw num one and coverage
 *   equal to the request.
 *
 * Encoding details:
 *   NUM = 0 (raw num = 1) and SCALE = log2(num_grans).
 *
 *   Example: num_grans = 8
 *   covered = 1 * 2^3 = 8
 *
 *   Spec: Range = (0 + 1) * 2^3 = 8 granules
 *   Exercise exponents 1..39, using the FEAT_DS limit above exponent 31.
 *   Exact fits should retain the largest scale with raw num = 1.
 */
TEST(smmuv3_tlbi_range, powers_of_2)
{
	for (unsigned int i = 1U; i <= SCALE_MAX_FEAT_DS; i++) {
		unsigned int scale, scale_max;
		unsigned long num, covered;
		unsigned long ng = 1UL << i;

		scale_max = (i > SCALE_MAX_NO_DS) ? SCALE_MAX_FEAT_DS : SCALE_MAX_NO_DS;
		covered = calc_tlbi_range(ng, scale_max, &scale, &num);

		UNSIGNED_LONGS_EQUAL(i, scale);
		UNSIGNED_LONGS_EQUAL(1UL, num);
		UNSIGNED_LONGS_EQUAL(ng, covered);
	}
}

/*
 * TC3: Large raw counts that fit in one command.
 *
 * Public APIs tested:
 *   calc_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify exact coverage with a large raw count at several scales.
 *
 * Method:
 *   Calculate chunks for 31, 62 and 124 granules using scale limit 31.
 *
 * Expected results:
 *   Raw num is 31 for every case, scales are 0, 1 and 2, and each request is
 *   fully covered.
 *
 * Encoding details:
 *   For num_grans = 31, scale = 0 and raw num = 31 give encoded NUM = 30.
 *
 *   num_grans = 31
 *   scale = 0
 *   num = 31
 *   covered = 31 * 2^0 = 31
 *
 *   Also: num_grans = 62 (31 * 2):  scale = 1, num = 31, covered = 62.
 *         num_grans = 31 * 4 = 124: scale = 2, num = 31, covered = 124.
 *   Scaling the request must preserve the raw count and exact coverage.
 */
TEST(smmuv3_tlbi_range, max_num_one_shot)
{
	unsigned int scale;
	unsigned long num, covered;

	/* num_grans = 31 = 31 * 2^0 */
	covered = calc_tlbi_range(31UL, SCALE_MAX_NO_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(0U, scale);
	UNSIGNED_LONGS_EQUAL(31UL, num);
	UNSIGNED_LONGS_EQUAL(31UL, covered);

	/* num_grans = 62 = 31 * 2^1 */
	covered = calc_tlbi_range(62UL, SCALE_MAX_NO_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(1U, scale);
	UNSIGNED_LONGS_EQUAL(31UL, num);
	UNSIGNED_LONGS_EQUAL(62UL, covered);

	/* num_grans = 124 = 31 * 2^2 */
	covered = calc_tlbi_range(124UL, SCALE_MAX_NO_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(2U, scale);
	UNSIGNED_LONGS_EQUAL(31UL, num);
	UNSIGNED_LONGS_EQUAL(124UL, covered);
}

/*
 * TC4: Non-power-of-2 values.
 *
 * Public APIs tested:
 *   calc_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify that odd and even non-power-of-two requests retain exact coverage.
 *
 * Method:
 *   Calculate chunks for 6, 7, 3 and 10 granules using scale limit 31.
 *
 * Expected results:
 *   The (scale, raw num) pairs are (1, 3), (0, 7), (0, 3) and (1, 5);
 *   coverage equals each input.
 *
 * Encoding details:
 *   Odd and even requests must fit exactly by combining the scale with a
 *   raw count greater than one, without rounding up to a power of two.
 *
 *   num_grans = 3 => scale = 0, num = 3, covered = 3.
 *	Spec: (2 + 1) * 2^0 = 3.
 *
 *   num_grans = 6 => scale = 1, num = 3,  covered = 6.
 *	Spec: (2 + 1) * 2^1 = 6.
 *
 *   num_grans = 7 => scale = 0, num = 7, covered = 7.
 *	Spec: (6 + 1) * 2^0 = 7.
 *
 *   num_grans = 10 => scale = 1, num = 5, covered = 10.
 *	Spec: (4 + 1) * 2^1 = 10.
 */
TEST(smmuv3_tlbi_range, non_power_of_2)
{
	unsigned int scale;
	unsigned long num, covered;

	/* 6 */
	covered = calc_tlbi_range(6UL, SCALE_MAX_NO_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(1U, scale);
	UNSIGNED_LONGS_EQUAL(3UL, num);
	UNSIGNED_LONGS_EQUAL(6UL, covered);

	/* 7 */
	covered = calc_tlbi_range(7UL, SCALE_MAX_NO_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(0U, scale);
	UNSIGNED_LONGS_EQUAL(7UL, num);
	UNSIGNED_LONGS_EQUAL(7UL, covered);

	/* 3 */
	covered = calc_tlbi_range(3UL, SCALE_MAX_NO_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(0U, scale);
	UNSIGNED_LONGS_EQUAL(3UL, num);
	UNSIGNED_LONGS_EQUAL(3UL, covered);

	/* 10 */
	covered = calc_tlbi_range(10UL, SCALE_MAX_NO_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(1U, scale);
	UNSIGNED_LONGS_EQUAL(5UL, num);
	UNSIGNED_LONGS_EQUAL(10UL, covered);
}

/*
 * TC5: Two-iteration case -- values that cannot be covered in one command.
 *
 * Public APIs tested:
 *   calc_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify decomposition at a one-granule remainder and the largest-scale tie
 *   break.
 *
 * Method:
 *   Calculate a chunk for 33 granules, then a second chunk for the remaining
 *   granule.
 *
 * Expected results:
 *   The chunks cover 32 and 1 granules, with (scale, raw num) equal to (5, 1)
 *   and (0, 1).
 *
 * Encoding details:
 *
 *   num_grans = 33 = (1 * 2^5) + 1
 *
 *   The bounded search selects SCALE = 5, num = 1 (encoded NUM = 0) as the
 *   best single-command option, leaving 1 granule for the second iteration.
 *   Ties (equal covered values at lower SCALE) are broken in favour of the
 *   larger SCALE, so scale = 5 is selected over scale = 4..0.
 *   The two calls must cover 32 and 1 granules without overshooting 33.
 */
TEST(smmuv3_tlbi_range, two_iteration_values)
{
	unsigned int scale;
	unsigned long num, covered;

	/* First iteration: covers 32 granules (scale=5, num=1) */
	covered = calc_tlbi_range(33UL, SCALE_MAX_NO_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(5U, scale);
	UNSIGNED_LONGS_EQUAL(1UL, num);
	UNSIGNED_LONGS_EQUAL(32UL, covered);

	/* Second iteration: remaining 1 granule */
	covered = calc_tlbi_range(1UL, SCALE_MAX_NO_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(0U, scale);
	UNSIGNED_LONGS_EQUAL(1UL, num);
	UNSIGNED_LONGS_EQUAL(1UL, covered);
}

/*
 * TC6: Scale clamping -- no FEAT_DS (scale_max = 31).
 *
 * Public APIs tested:
 *   calc_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify clamping at scale 31 and saturation of the raw count.
 *
 * Method:
 *   Calculate chunks for 2^32, 2^35, 2^36 and 2^37 granules using scale limit
 *   31.
 *
 * Expected results:
 *   All scales are 31 and raw counts are 2, 16, 32 and 32. Coverage is exact
 *   for the first three inputs; the final chunk covers only 2^36 granules.
 *
 * Encoding details:
 *
 *   Scale clamping occurs when hi > scale_max (hi = floor_log2(num_grans)).
 *   In that case s_hi is clamped to scale_max and the bounded search
 *   finds the best (NUM, SCALE = scale_max) pair without exceeding
 *   num_grans.
 *
 *   num_grans = 2^32:  hi=32 > 31, s_hi=31.
 *     Bounded search at s=31: num = 2^32 >> 31 = 2.
 *     covered = 2 << 31 = 2^32  (perfect fit).
 *
 *   num_grans = 2^35:  hi=35 > 31, s_hi=31.
 *     num = 2^35 >> 31 = 16.  covered = 16 << 31 = 2^35.
 *
 *   num_grans = 2^36:  s_hi=31.
 *     num = 2^36 >> 31 = 32 == NUM_FIELD_MAX.
 *
 *   num_grans = 2^37:  hi=37, s_lo = max(0, 37-5) = 32 > s_hi=31,
 *     so s_lo is clamped to s_hi=31.  num = MIN(2^37>>31, 32) = 32.
 *     covered = 32 << 31 = 2^36 (not 2^37 -- takes two iterations).
 *   These cases cross the scale limit, then the maximum count at that scale.
 */
TEST(smmuv3_tlbi_range, scale_clamp_no_ds)
{
	unsigned int scale;
	unsigned long num, covered;

	/* 2^32: scale = 32 > 31, num = 2, scale_out = 31, covered = 2 << 31 = 2^32 */
	covered = calc_tlbi_range(1UL << 32, SCALE_MAX_NO_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(SCALE_MAX_NO_DS, scale);
	UNSIGNED_LONGS_EQUAL(2UL, num);
	UNSIGNED_LONGS_EQUAL(1UL << 32, covered);

	/* 2^35: num = 16, scale = 31, covered = 2^35 */
	covered = calc_tlbi_range(1UL << 35, SCALE_MAX_NO_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(SCALE_MAX_NO_DS, scale);
	UNSIGNED_LONGS_EQUAL(16UL, num);
	UNSIGNED_LONGS_EQUAL(1UL << 35, covered);

	/* 2^36: num = 32 == NUM_FIELD_MAX, scale = 31, covered = 2^36 */
	covered = calc_tlbi_range(1UL << 36, SCALE_MAX_NO_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(SCALE_MAX_NO_DS, scale);
	UNSIGNED_LONGS_EQUAL(NUM_FIELD_MAX, num);
	UNSIGNED_LONGS_EQUAL(1UL << 36, covered);

	/*
	 * 2^37: num would be 64 > NUM_FIELD_MAX = 32, so it is capped.
	 * covered = 32 << 31 = 2^36 (not 2^37 -- takes two iterations).
	 */
	covered = calc_tlbi_range(1UL << 37, SCALE_MAX_NO_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(SCALE_MAX_NO_DS, scale);
	UNSIGNED_LONGS_EQUAL(NUM_FIELD_MAX, num);          /* capped at 32 */
	UNSIGNED_LONGS_EQUAL(1UL << 36, covered);          /* not 2^37    */
	/* Verify: covered < num_grans (two iterations needed) */
	CHECK_TRUE(covered < (1UL << 37));
}

/*
 * TC7: Scale clamping -- with FEAT_DS (scale_max = 39).
 *
 * Public APIs tested:
 *   calc_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify the larger scale limit and saturation with FEAT_DS.
 *
 * Method:
 *   Calculate chunks for 2^40, 2^44 and 2^45 granules using scale limit 39.
 *
 * Expected results:
 *   All scales are 39 and raw counts are 2, 32 and 32. The first two requests
 *   fit exactly; the last chunk covers 2^44 granules.
 *
 * Encoding details:
 *
 *   num_grans = 2^40:  hi=40 > 39, s_hi=39.
 *     Bounded search at s=39: num = 2^40 >> 39 = 2.
 *     covered = 2 << 39 = 2^40  (perfect fit).
 *
 *   num_grans = 2^44:  hi=44 > 39, s_hi=39, s_lo = max(0, 44-5) = 39.
 *     Single candidate at s=39: num = 2^44 >> 39 = 32 == NUM_FIELD_MAX.
 *     covered = 32 << 39 = 2^44  (perfect fit).
 *
 *   num_grans = 2^45:  s_hi=39, s_lo = max(0, 45-5) = 40 > 39,
 *     so s_lo is clamped to s_hi=39.  num = MIN(2^45>>39, 32) = 32.
 *     covered = 32 << 39 = 2^44 (not 2^45 -- takes two iterations).
 *   Check both exact coverage at the FEAT_DS limit and saturation beyond it.
 */
TEST(smmuv3_tlbi_range, scale_clamp_feat_ds)
{
	unsigned int scale;
	unsigned long num, covered;

	/* 2^40 with FEAT_DS: scale = 40 > 39, num = 2, scale_out = 39, covered = 2^40 */
	covered = calc_tlbi_range(1UL << 40, SCALE_MAX_FEAT_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(SCALE_MAX_FEAT_DS, scale);
	UNSIGNED_LONGS_EQUAL(2UL, num);
	UNSIGNED_LONGS_EQUAL(1UL << 40, covered);

	/* 2^44: num = 1 << 5 = 32 = NUM_FIELD_MAX, covered = 2^44 */
	covered = calc_tlbi_range(1UL << 44, SCALE_MAX_FEAT_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(SCALE_MAX_FEAT_DS, scale);
	UNSIGNED_LONGS_EQUAL(NUM_FIELD_MAX, num);
	UNSIGNED_LONGS_EQUAL(1UL << 44, covered);

	/* 2^45: num capped to 32, covered = 32 << 39 = 2^44 (not 2^45) */
	covered = calc_tlbi_range(1UL << 45, SCALE_MAX_FEAT_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(SCALE_MAX_FEAT_DS, scale);
	UNSIGNED_LONGS_EQUAL(NUM_FIELD_MAX, num);
	UNSIGNED_LONGS_EQUAL(1UL << 44, covered);
	CHECK_TRUE(covered < (1UL << 45));
}

/*
 * TC8: Coverage completeness -- small values (1..128).
 *
 * Public APIs tested:
 *   calc_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify iterative progress and exact total coverage for small requests.
 *
 * Method:
 *   For every count from 1 through 128, repeatedly calculate and subtract
 *   chunks with both scale limits.
 *
 * Expected results:
 *   Every chunk satisfies the coverage formula and field bounds, is nonzero,
 *   and stays within the remainder. The accumulated coverage equals the
 *   requested total.
 *
 * Encoding details:
 *
 *   For every num_grans in 1..128, the iterative loop must cover exactly
 *   num_grans granules total.  No granule may be missed or double-counted.
 *   Run with both scale limits and check progress, field bounds and the
 *   coverage formula at every step, including remainders after large chunks.
 */
TEST(smmuv3_tlbi_range, coverage_completeness_small)
{
	for (unsigned long ng = 1UL; ng <= 128UL; ng++) {
		check_full_coverage(ng, SCALE_MAX_NO_DS);
		check_full_coverage(ng, SCALE_MAX_FEAT_DS);
	}
}

/*
 * TC9: Coverage completeness -- one S2TT and its adjacent granule counts.
 *
 * Public APIs tested:
 *   calc_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify decomposition around a table-sized granule count.
 *
 * Method:
 *   Check the exact fields for 512 granules, then iterate complete coverage
 *   for 511, 512 and 513 granules using scale limit 31.
 *
 * Expected results:
 *   The 512-granule chunk uses scale 9 and raw num one. All three totals are
 *   covered exactly with legal, nonzero chunks.
 *
 * Encoding details:
 *
 *   S2TTES_PER_S2TT = 512 = 2^9: single command with NUM = 0, SCALE = 9.
 *   Check exact fields for 512, then full coverage for 511, 512 and 513.
 *   The neighboring counts exercise splitting just below and above a power
 *   of two, where a one-granule remainder can otherwise be lost.
 */
TEST(smmuv3_tlbi_range, coverage_completeness_s2tt_sizes)
{
	unsigned int scale;
	unsigned long num, covered;

	/* 512 = S2TTES_PER_S2TT */
	covered = calc_tlbi_range(512UL, SCALE_MAX_NO_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(9U, scale);
	UNSIGNED_LONGS_EQUAL(1UL, num);
	UNSIGNED_LONGS_EQUAL(512UL, covered);

	check_full_coverage(512UL, SCALE_MAX_NO_DS);
	check_full_coverage(511UL, SCALE_MAX_NO_DS);  /* one short of power-of-2 */
	check_full_coverage(513UL, SCALE_MAX_NO_DS);  /* one over power-of-2 */
}

/*
 * TC10: Coverage completeness -- large scale-clamped values.
 *
 * Public APIs tested:
 *   calc_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify complete coverage when requests exceed a single clamped chunk.
 *
 * Method:
 *   Iterate coverage for 2^37, 2^38 and 3 * 2^31 granules with limit 31, and
 *   2^45 granules with limit 39.
 *
 * Expected results:
 *   Each decomposition terminates with exactly the requested total and no
 *   overshoot; every chunk has legal fields and matches raw num << scale.
 *
 * Encoding details:
 *
 *   Verify that values requiring multiple iterations due to scale clamping
 *   are still fully covered under both architectural scale limits. Include
 *   3 * 2^31 as an exact fit with a raw count greater than one, alongside
 *   requests that need two or four maximum-sized chunks.
 */
TEST(smmuv3_tlbi_range, coverage_completeness_large)
{
	/* 2^37 needs 2 iterations with scale_max = 31 */
	check_full_coverage(1UL << 37, SCALE_MAX_NO_DS);

	/* 2^38 needs 4 iterations with scale_max = 31 */
	check_full_coverage(1UL << 38, SCALE_MAX_NO_DS);

	/* 2^45 needs 2 iterations with scale_max = 39 */
	check_full_coverage(1UL << 45, SCALE_MAX_FEAT_DS);

	/* 3 * 2^31: scale = 31, num = 3, covered in one shot */
	check_full_coverage(3UL << 31, SCALE_MAX_NO_DS);
}

/*
 * TC11: NUM field validity.
 *
 * Public APIs tested:
 *   calc_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify that raw num can always be encoded as a five-bit NUM field.
 *
 * Method:
 *   Calculate chunks for the representative input list, including boundaries
 *   around powers of two and large scale-clamped values, using limit 31.
 *
 * Expected results:
 *   Raw num is in [1, 32], scale is at most 31, coverage equals raw num <<
 *   scale and never exceeds the input.
 *
 * Encoding details:
 *
 *   The NUM field in the SMMU command is NUM_WIDTH bits wide.  The encoded
 *   value is (num - 1), so num must satisfy 1 <= num <= 2^NUM_WIDTH = 32.
 *
 *   Test representative inputs to confirm num is always in [1, 32].
 *   Counts around powers of two and the no-FEAT_DS scale limit exercise
 *   count saturation; also check the scale, formula and non-overshoot bound.
 */
TEST(smmuv3_tlbi_range, num_field_always_valid)
{
	static const unsigned long test_inputs[] = {
		1UL, 2UL, 3UL, 7UL, 15UL, 31UL, 32UL, 33UL, 63UL, 64UL,
		127UL, 128UL, 255UL, 256UL, 512UL,
		1UL << 20, 1UL << 31, 1UL << 32, 1UL << 36
	};

	for (unsigned int i = 0U; i < ARRAY_SIZE(test_inputs); i++) {
		unsigned int scale;
		unsigned long num, covered;

		covered = calc_tlbi_range(test_inputs[i], SCALE_MAX_NO_DS,
					  &scale, &num);

		/* num in [1, 2^NUM_WIDTH] so (num - 1) fits in NUM_WIDTH bits */
		CHECK_TRUE(num >= 1UL);
		CHECK_TRUE(num <= NUM_FIELD_MAX);
		CHECK_TRUE(scale <= SCALE_MAX_NO_DS);
		CHECK_TRUE(covered <= test_inputs[i]);
		UNSIGNED_LONGS_EQUAL(num << scale, covered);
	}
}

/*
 * TC12: SMMU spec formula verification.
 *
 * Public APIs tested:
 *   calc_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify the coverage equation independently of fixed expected encodings.
 *
 * Method:
 *   Calculate one chunk for each listed small, uneven and scale-clamped input
 *   under its specified scale limit.
 *
 * Expected results:
 *   Coverage equals raw num << scale, does not exceed the input, and all raw
 *   counts and scales stay within their bounds.
 *
 * Encoding details:
 *
 *   The spec states:
 *     Range = (NUM + 1) * 2^SCALE * GRANULE_SIZE
 *
 *   With our notation (num = NUM + 1):
 *     granules_covered = num * 2^SCALE = num << scale = covered
 *
 *   Verify this identity for small, non-power-of-two and large clamped
 *   requests under both scale limits. Field-bound and non-overshoot checks
 *   ensure a matching formula cannot hide an invalid command encoding.
 */
TEST(smmuv3_tlbi_range, spec_formula_holds)
{
	static const struct {
		unsigned long num_grans;
		unsigned int scale_max;
	} cases[] = {
		{1UL,        SCALE_MAX_NO_DS},
		{8UL,        SCALE_MAX_NO_DS},
		{31UL,       SCALE_MAX_NO_DS},
		{62UL,       SCALE_MAX_NO_DS},
		{100UL,      SCALE_MAX_NO_DS},
		{512UL,      SCALE_MAX_NO_DS},
		{1UL << 32,  SCALE_MAX_NO_DS},
		{1UL << 36,  SCALE_MAX_NO_DS},
		{1UL << 40,  SCALE_MAX_FEAT_DS},
		{1UL << 44,  SCALE_MAX_FEAT_DS},
	};

	for (unsigned int i = 0U; i < ARRAY_SIZE(cases); i++) {
		unsigned int scale;
		unsigned long num, covered;

		covered = calc_tlbi_range(cases[i].num_grans, cases[i].scale_max,
					  &scale, &num);
		/*
		 * Core spec identity:
		 *   covered == (NUM + 1) * 2^SCALE == num * 2^scale
		 */
		UNSIGNED_LONGS_EQUAL(num << scale, covered);

		/* covered must not exceed the requested range */
		CHECK_TRUE(covered <= cases[i].num_grans);

		/* Architectural field limits */
		CHECK_TRUE(num >= 1UL);
		CHECK_TRUE(num <= NUM_FIELD_MAX);
		CHECK_TRUE(scale <= cases[i].scale_max);
	}
}

/*
 * TC13: Count commands for powers of two minus one.
 *
 * Public APIs tested:
 *   calc_tlbi_range() (internal helper).
 *
 * Aim:
 *   Guard the command count for decompositions of large odd requests.
 *
 * Method:
 *   Decompose every 2^n - 1 request for n from 6 through 44 using scale limit
 *   39. Print each sequence and accumulate the number of chunks.
 *
 * Expected results:
 *   All decompositions reach zero and the aggregate number of chunks is
 *   exactly 211. This test checks the aggregate count; the neighboring
 *   coverage tests check per-chunk field bounds.
 *
 * Encoding details:
 *   Each request is the sum of its chunks:
 *   num_0 * 2^SCALE_0 + ... num_n * 2^SCALE_n, where num = NUM + 1.
 *
 *   Display the command sequence for granule counts from (2^6 - 1) to (2^44 - 1),
 *   where each step is (2^n - 1) for n = 6..44.
 *   Require exactly 211 commands across the sweep to detect a regression in
 *   the decomposition's command count, even if all ranges are still covered.
 */
TEST(smmuv3_tlbi_range, powers_of_2_minus_1)
{
	unsigned int total = 0U;

	INFO("\n");

	/* Covers all 4KB granules in the 56-bit address space */
	for (unsigned int i = 6U; i <= 44U; i++) {
		/* Number of granules 2^i - 1 */
		unsigned long ng = (1UL << i) - 1UL;
		unsigned int cmds = 0U;

		INFO("0x%011lx = ", ng);

		while (true) {
			unsigned long num, covered;
			unsigned int scale;

			covered = calc_tlbi_range(ng, SCALE_MAX_FEAT_DS, &scale, &num);

			if (scale == 0U) {
				INFO("%lu", num);
			} else {
				INFO("%lu*2^%u", num, scale);
			}

			cmds++;
			ng -= covered;

			if (ng == 0UL) {
				INFO("\n%u commands\n", cmds);
				break;
			}

			INFO(" + ");
		}

		total += cmds;
	}

	INFO("Total number of commands %u\n", total);

	/*
	 * Regression guard: the optimized algorithm must produce exactly 211
	 * commands across all 39 inputs (i = 6..44) with scale_max = 39.
	 */
	UNSIGNED_LONGS_EQUAL(211U, total);
}

/*
 * TC14: Optimization quality -- first-iteration SCALE maximization.
 *
 * Public APIs tested:
 *   calc_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify the first chunk maximizes coverage for large odd requests.
 *
 * Method:
 *   Check explicit examples, then sweep inputs 2^n - 1 for n from 6 through
 *   44 using scale limit 39.
 *
 * Expected results:
 *   The first chunk has scale n - NUM_WIDTH and raw num 31. Coverage is
 *   31 << (n - NUM_WIDTH), including the scale-39 endpoint.
 *
 * Encoding details:
 *
 *   For inputs of the form (2^n - 1) the previous LSB-based algorithm
 *   always selected SCALE = 0 (the input is odd) and raw num = 31, covering
 *   only 31 granules per command regardless of n.
 *
 *   The bounded-search algorithm selects the (SCALE, NUM) pair that
 *   maximises coverage.  For n in [NUM_WIDTH + 1, scale_max + NUM_WIDTH]:
 *
 *     SCALE = n - NUM_WIDTH, num = 31 (encoded NUM = 30),
 *     covered = 31 * 2^(n - NUM_WIDTH)   (31/32 of 2^n granules in one shot)
 *
 *   This is verified both for specific inputs and via a loop over the
 *   full range n = [NUM_WIDTH + 1, SCALE_MAX_FEAT_DS + NUM_WIDTH].
 */
TEST(smmuv3_tlbi_range, first_iter_scale_maximization)
{
	unsigned int scale;
	unsigned long num, covered;

	/* 2^6 - 1 = 63: optimal SCALE = 1, num = 31, covered = 62 */
	covered = calc_tlbi_range(63UL, SCALE_MAX_FEAT_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(1U, scale);
	UNSIGNED_LONGS_EQUAL(31UL, num);
	UNSIGNED_LONGS_EQUAL(62UL, covered);

	/* 2^10 - 1 = 1023: optimal SCALE = 5, num = 31, covered = 31 * 32 = 992 */
	covered = calc_tlbi_range(1023UL, SCALE_MAX_FEAT_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(5U, scale);
	UNSIGNED_LONGS_EQUAL(31UL, num);
	UNSIGNED_LONGS_EQUAL(31UL << 5, covered);

	/* 2^12 - 1 = 4095: optimal SCALE = 7, num = 31, covered = 31 * 128 = 3968 */
	covered = calc_tlbi_range(4095UL, SCALE_MAX_FEAT_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(7U, scale);
	UNSIGNED_LONGS_EQUAL(31UL, num);
	UNSIGNED_LONGS_EQUAL(31UL << 7, covered);

	/* 2^44 - 1: optimal SCALE = 39 (= scale_max), num = 31 */
	covered = calc_tlbi_range((1UL << 44) - 1UL, SCALE_MAX_FEAT_DS, &scale, &num);
	UNSIGNED_LONGS_EQUAL(SCALE_MAX_FEAT_DS, scale);
	UNSIGNED_LONGS_EQUAL(31UL, num);
	UNSIGNED_LONGS_EQUAL(31UL << SCALE_MAX_FEAT_DS, covered);

	/*
	 * Loop: for all n in [NUM_WIDTH+1, SCALE_MAX_FEAT_DS+NUM_WIDTH],
	 * i.e. n in [6, 44], verify:
	 *   first call on (2^n - 1) returns SCALE = n - NUM_WIDTH, num = 31.
	 */
	for (unsigned int n = NUM_WIDTH + 1U;
	     n <= SCALE_MAX_FEAT_DS + NUM_WIDTH; n++) {
		unsigned long ng = (1UL << n) - 1UL;
		unsigned int expected_scale = n - NUM_WIDTH;

		covered = calc_tlbi_range(ng, SCALE_MAX_FEAT_DS, &scale, &num);
		UNSIGNED_LONGS_EQUAL(expected_scale, scale);
		UNSIGNED_LONGS_EQUAL(31UL, num);
		UNSIGNED_LONGS_EQUAL(31UL << expected_scale, covered);
	}
}

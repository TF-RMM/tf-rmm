/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 * Unit tests for calc_tlbi_range().
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
 * The tests here prove:
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

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <debug.h>
#include <smc-rmi.h>
#include <smmuv3_priv.h>
#include <test_helpers.h>
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

TEST_GROUP(smmuv3_tlbi_range)
{
};

/* -----------------------------------------------------------------------
 * TC1: Single granule -- the minimal possible input.
 *
 *   num_grans = 1 = 0b1
 *   trailing zeros = 0  =>  scale = 0
 *   num = (1 >> 0) & 31 = 1
 *   covered = 1 * 2^0 = 1
 *
 *   Spec: Range = (NUM + 1) * 2^SCALE = (0 + 1) * 1 = 1 granule
 * ----------------------------------------------------------------------- */
TEST(smmuv3_tlbi_range, single_granule)
{
	unsigned int scale;
	unsigned long num, covered;

	covered = calc_tlbi_range(1UL, SCALE_MAX_NO_DS, &scale, &num);

	UNSIGNED_LONGS_EQUAL(0U, scale);
	UNSIGNED_LONGS_EQUAL(1UL, num);
	UNSIGNED_LONGS_EQUAL(1UL, covered);
}

/* -----------------------------------------------------------------------
 * TC2: Powers of 2 -- each should be covered in exactly one command with
 *   NUM = 0 (raw num = 1) and SCALE = log2(num_grans).
 *
 *   Example: num_grans = 8
 *   covered = 1 * 2^3 = 8
 *
 *   Spec: Range = (0 + 1) * 2^3 = 8 granules
 * ----------------------------------------------------------------------- */
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

/* -----------------------------------------------------------------------
 * TC3: Maximum one-shot coverage -- values that fit in NUM (<= 31) with
 *   scale = 0, num_grans = 31 uses NUM = 30 (raw num = 31).
 *
 *   num_grans = 31
 *   scale = 0
 *   num = 31
 *   covered = 31 * 2^0 = 31
 *
 *   Also: num_grans = 62 (31 * 2):  scale = 1, num = 31, covered = 62.
 *         num_grans = 31 * 4 = 124: scale = 2, num = 31, covered = 124.
 * ----------------------------------------------------------------------- */
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

/* ----------------------------------------------------------------------------------
 * TC4: Non-power-of-2 values.
 *
 *   num_grans = 3 => scale = 0, num = 3, covered = 3.
 *	Spec: (2 + 1) * 2^1 = 3.
 *
 *   num_grans = 6 => scale = 1, num = 3,  covered = 6.
 *	Spec: (2 + 1) * 2^1 = 6.
 *
 *   num_grans = 7 => scale = 0, num = 7, covered = 7.
 *	Spec: (6 + 1) * 2^0 = 7.
 *
 *   num_grans = 10 => scale = 1, num = 5, covered = 10.
 *	Spec: (4 + 1) * 2^1 = 10.
 * ---------------------------------------------------------------------------------- */
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

/* ---------------------------------------------------------------------------
 * TC5: Two-iteration case -- values that cannot be covered in one command.
 *
 *   num_grans = 33 = 1 + (1 * 2^5)
 * --------------------------------------------------------------------------- */
TEST(smmuv3_tlbi_range, two_iteration_values)
{
	unsigned int scale;
	unsigned long num, covered;

	/* num_grans = 33 */
	covered = calc_tlbi_range(33UL, SCALE_MAX_NO_DS, &scale, &num);
	if (covered == 1UL) {
		/* First iteration covers 1 granule */
		UNSIGNED_LONGS_EQUAL(0U, scale);
		UNSIGNED_LONGS_EQUAL(1UL, num);

		/* Second iteration: remaining 32  */
		covered = calc_tlbi_range(32UL, SCALE_MAX_NO_DS, &scale, &num);
		UNSIGNED_LONGS_EQUAL(5U, scale);
		UNSIGNED_LONGS_EQUAL(1UL, num);
		UNSIGNED_LONGS_EQUAL(32UL, covered);
	} else {
		/* First iteration covers 32 granules */
		UNSIGNED_LONGS_EQUAL(32UL, covered);
		UNSIGNED_LONGS_EQUAL(5U, scale);
		UNSIGNED_LONGS_EQUAL(1UL, num);

		/* Second iteration: remaining 1  */
		covered = calc_tlbi_range(1UL, SCALE_MAX_NO_DS, &scale, &num);
		UNSIGNED_LONGS_EQUAL(0U, scale);
		UNSIGNED_LONGS_EQUAL(1UL, num);
		UNSIGNED_LONGS_EQUAL(1UL, covered);
	}
}

/* -----------------------------------------------------------------------
 * TC6: Scale clamping -- no FEAT_DS (scale_max = 31).
 *
 *   When num_grans has trailing zeros count > scale_max (31), the SCALE
 *   field is clamped and NUM is increased to compensate.
 *
 *   num_grans = 2^32:  trailing zeros = 32 > 31.
 *     num = 1 << (32 - 31) = 2.  scale_out = 31.
 *     covered = 2 << 31 = 2^32.
 *
 *   num_grans = 2^35:  trailing zeros = 35 > 31.
 *     num = 1 << (35 - 31) = 16.  scale_out = 31.
 *     covered = 16 << 31 = 2^35.
 *
 *   num_grans = 2^36:  num = 1 << 5 = 32 (== NUM_FIELD_MAX).
 *
 *   num_grans = 2^37:  num would be 1 << 6 = 64 > NUM_FIELD_MAX=32.
 *     Capped: num = 32, scale = 31, covered = 32 << 31 = 2^36.
 *     Only covers half; second iteration handles the rest.
 * ----------------------------------------------------------------------- */
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

/* -----------------------------------------------------------------------
 * TC7: Scale clamping -- with FEAT_DS (scale_max = 39).
 *
 *   num_grans = 2^40: trailing zeros = 40 > 39.
 *     num = 1 << (40 - 39) = 2.  scale_out = 39.  covered = 2 << 39 = 2^40.
 *
 *   num_grans = 2^44: num = 1 << (44 - 39) = 32 == NUM_FIELD_MAX.
 *
 *   num_grans = 2^45: num would be 64, capped at 32.
 *     covered = 32 << 39 = 2^44 (not 2^45).
 * ----------------------------------------------------------------------- */
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

/* -----------------------------------------------------------------------
 * TC8: Coverage completeness -- small values (1..128).
 *
 *   For every num_grans in 1..128, the iterative loop must cover exactly
 *   num_grans granules total.  No granule may be missed or double-counted.
 * ----------------------------------------------------------------------- */
TEST(smmuv3_tlbi_range, coverage_completeness_small)
{
	for (unsigned long ng = 1UL; ng <= 128UL; ng++) {
		check_full_coverage(ng, SCALE_MAX_NO_DS);
		check_full_coverage(ng, SCALE_MAX_FEAT_DS);
	}
}

/* -----------------------------------------------------------------------
 * TC9: Coverage completeness -- S2TT sizes (512 and 1024 entries).
 *
 *   S2TTES_PER_S2TT = 512 = 2^9: single command with NUM = 0, SCALE = 9.
 * ----------------------------------------------------------------------- */
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

/* -----------------------------------------------------------------------
 * TC10: Coverage completeness -- large scale-clamped values.
 *
 *   Verify that values requiring multiple iterations due to scale clamping
 *   are still fully covered.
 * ----------------------------------------------------------------------- */
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

/* -----------------------------------------------------------------------
 * TC11: NUM field validity.
 *
 *   The NUM field in the SMMU command is NUM_WIDTH bits wide.  The encoded
 *   value is (num - 1), so num must satisfy 1 <= num <= 2^NUM_WIDTH = 32.
 *
 *   Test representative inputs to confirm num is always in [1, 32].
 * ----------------------------------------------------------------------- */
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

/* -----------------------------------------------------------------------
 * TC12: SMMU spec formula verification.
 *
 *   The spec states:
 *     Range = (NUM + 1) * 2^SCALE * GRANULE_SIZE
 *
 *   With our notation (num = NUM + 1):
 *     granules_covered = num * 2^SCALE = num << scale = covered
 *
 *   Verify this identity holds for a representative set of inputs.
 * ----------------------------------------------------------------------- */
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

/* ------------------------------------------------------------------------------
 * TC13: Powers of 2 minus 1 -- each will be covered in a number of commands
 *   NUM_0 * 2^SCALE_0 + ... NUM_n * 2^SCALE_n
 *
 *   Display the command sequence for granule counts from (2^6 - 1) to (2^44 - 1),
 *   where each step is (2^n - 1) for n = 6..44.
 * ------------------------------------------------------------------------------ */
TEST(smmuv3_tlbi_range, powers_of_2_minus_1)
{
	unsigned int total = 0U;

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
}

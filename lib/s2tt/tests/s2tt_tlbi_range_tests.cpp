/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 * CPU TLBI tests observe VTTBR_EL2 writes through the fake-host callbacks.
 * The shared fixture seeds VMID 0xBEEF and a nonzero base/control value so
 * restoration checks cover the whole register, not only the VMID field.
 * These checks observe context selection and restoration; they do not
 * observe hardware TLB contents or execution of the invalidation itself.
 * Range-helper tests below exercise encoding arithmetic without host boot.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_helpers.h>
#include <assert.h>
#include <host_utils.h>
#include <s2tt.h>
#include <s2tt_pvt_defs.h>
#include <sizes.h>
#include <test_helpers.h>
}

/* Distinct VMID and nonzero base exercise restoration of the whole register. */
static const u_register_t initial_vttbr = INPLACE(VTTBR_EL2_VMID, 0xBEEFUL) | 0x12345001UL;
static u_register_t vttbr_writes[4];
static unsigned int vttbr_write_count;
static const bool lpa2_modes[] = {false, true};

/* Return the emulated register while observing S2TT's VMID switches. */
static u_register_t read_vttbr(u_register_t *reg)
{
	return *reg;
}

/* Record every write, including restoration; the test allows at most three VMIDs. */
static void write_vttbr(u_register_t value, u_register_t *reg)
{
	CHECK_TRUE(vttbr_write_count < ARRAY_SIZE(vttbr_writes));
	vttbr_writes[vttbr_write_count++] = value;
	*reg = value;
}

/*
 * Check that an invalidation selected exactly @nvmids entries from @vmids,
 * then restored the full original VTTBR_EL2. Call after each API invocation.
 * Reset only the observation count so the next call starts from that register.
 */
static void check_vmid_switches(const unsigned int *vmids, unsigned int nvmids)
{
	CHECK_EQUAL(nvmids + 1U, vttbr_write_count);
	for (unsigned int i = 0U; i < nvmids; i++) {
		UNSIGNED_LONGS_EQUAL(INPLACE(VTTBR_EL2_VMID, vmids[i]), vttbr_writes[i]);
	}
	UNSIGNED_LONGS_EQUAL(initial_vttbr, vttbr_writes[nvmids]);
	UNSIGNED_LONGS_EQUAL(initial_vttbr, read_vttbr_el2());
	vttbr_write_count = 0U;
}

/* Keep register-level invalidation checks local to S2TT unit tests. */
TEST_GROUP(s2tt_tlbi)
{
	/*
	 * Shared startup restores the boot register/callback snapshot before
	 * each test. Install this group's observer and seed its register here;
	 * the next startup discards them, so no callback teardown is needed.
	 */
	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start(false);
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
		vttbr_write_count = 0U;
		CHECK_EQUAL(0, host_util_set_sysreg_cb("vttbr_el2", read_vttbr, write_vttbr,
						    initial_vttbr));
	}
};

/*
 * TC1: Select one VMID for page and block invalidation.
 *
 * Public APIs tested:
 *   s2tt_invalidate_page_block().
 *
 * Aim:
 *   Verify that every supported block/page level uses the requested 16-bit
 *   VMID and restores the complete caller context.
 *
 * Method:
 *   With the VTTBR_EL2 observer installed, invalidate IPA SZ_1G for VMID
 *   0x1234 at levels S2TT_MIN_BLOCK_LEVEL through S2TT_PAGE_LEVEL. Repeat
 *   with LPA2 disabled and enabled; inspect and reset the write trace after
 *   each call.
 *
 * Expected results:
 *   Each call writes the requested VMID with other VTTBR_EL2 fields zero,
 *   then restores initial_vttbr. Exactly two writes occur and the final
 *   register equals its initial value.
 */
TEST(s2tt_tlbi, page_block_selects_vmid_and_restores_vttbr)
{
	unsigned int vmid = 0x1234U;

	for (bool lpa2 : lpa2_modes) {
		for (long level = S2TT_MIN_BLOCK_LEVEL; level <= S2TT_PAGE_LEVEL; level++) {
			s2tt_invalidate_page_block(lpa2, vmid, SZ_1G, level);
			check_vmid_switches(&vmid, 1U);
		}
	}
}

/*
 * TC2: Visit every VMID for page invalidation.
 *
 * Public APIs tested:
 *   s2tt_invalidate_page_block_per_vmids().
 *
 * Aim:
 *   Verify list order, inclusion of VMID zero and a 16-bit VMID, and
 *   restoration after the final invalidation.
 *
 * Method:
 *   Invalidate the page at SZ_1G for VMIDs {2, 0, 0x1234}, with LPA2 disabled
 *   and enabled. Observe all VTTBR_EL2 writes after each call.
 *
 * Expected results:
 *   Exactly four writes occur: one VMID-only value for each list entry in
 *   order, then the full initial_vttbr value. The final register matches the
 *   original context.
 */
TEST(s2tt_tlbi, page_block_visits_each_vmid_and_restores_vttbr)
{
	unsigned int vmids[] = {2U, 0U, 0x1234U};

	for (bool lpa2 : lpa2_modes) {
		s2tt_invalidate_page_block_per_vmids(lpa2, vmids, ARRAY_SIZE(vmids),
						    SZ_1G, S2TT_PAGE_LEVEL);
		check_vmid_switches(vmids, ARRAY_SIZE(vmids));
	}
}

/*
 * TC3: Preserve context around pages-in-block invalidation.
 *
 * Public APIs tested:
 *   s2tt_invalidate_pages_in_block().
 *
 * Aim:
 *   Verify that range and VMID-wide invalidation of a removed table select
 *   the requested VMID and restore the full caller VTTBR_EL2.
 *
 * Method:
 *   With the register observer installed, invalidate pages in the block at
 *   IPA zero for VMID 0x1234 at child levels 1 through 3. This exercises
 *   VMID-wide maintenance above 1GB and range maintenance at 1GB and 2MB.
 *   Repeat with LPA2 disabled and enabled.
 *
 * Expected results:
 *   Each call produces exactly two writes: the VMID-only value for 0x1234
 *   followed by initial_vttbr. Both the recorded restoration and final
 *   register retain the original VMID and base/control bits.
 */
TEST(s2tt_tlbi, pages_in_block_selects_vmid_and_restores_vttbr)
{
	unsigned int vmid = 0x1234U;

	for (bool lpa2 : lpa2_modes) {
		for (long level = S2TT_MIN_BLOCK_LEVEL; level <= S2TT_PAGE_LEVEL; level++) {
			s2tt_invalidate_pages_in_block(lpa2, vmid, 0UL, level);
			check_vmid_switches(&vmid, 1U);
		}
	}
}

/*
 * TC4: Visit every VMID for pages-in-block invalidation.
 *
 * Public APIs tested:
 *   s2tt_invalidate_pages_in_block_per_vmids().
 *
 * Aim:
 *   Verify that the block request covers each supplied VMID once in list
 *   order before restoring the caller context.
 *
 * Method:
 *   Invalidate pages in the block at IPA zero for VMIDs {2, 0, 0x1234}, in
 *   both LPA2 modes and at child levels 1 through 3, covering VMID-wide
 *   and range maintenance. Check the observer trace after each API call.
 *
 * Expected results:
 *   The three VMID-only writes match the list, including VMID zero. A fourth
 *   write restores initial_vttbr, and the final register equals that full
 *   value.
 */
TEST(s2tt_tlbi, pages_in_block_visits_each_vmid_and_restores_vttbr)
{
	unsigned int vmids[] = {2U, 0U, 0x1234U};

	for (bool lpa2 : lpa2_modes) {
		for (long level = S2TT_MIN_BLOCK_LEVEL; level <= S2TT_PAGE_LEVEL; level++) {
			s2tt_invalidate_pages_in_block_per_vmids(lpa2, vmids, ARRAY_SIZE(vmids),
								0UL, level);
			check_vmid_switches(vmids, ARRAY_SIZE(vmids));
		}
	}
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

/*
 * TC1: Use the non-range path for one granule.
 *
 * Public APIs tested:
 *   calc_s2_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify the sentinel that directs the caller to use a single-address TLBI
 *   when a range encoding cannot describe one granule.
 *
 * Method:
 *   Call the helper with one granule and inspect both its return value and
 *   raw count output; no host boot or register observer is needed.
 *
 * Expected results:
 *   Coverage and raw num are both zero, selecting the caller's non-range
 *   path. The test makes no assertion about the scale output.
 */
TEST(s2tt_tlbi_range, single_granule_uses_non_range_tlbi)
{
	unsigned long num;
	unsigned int scale;

	UNSIGNED_LONGS_EQUAL(0UL, calc_s2_tlbi_range(1UL, &scale, &num));
	UNSIGNED_LONGS_EQUAL(0UL, num);
}

/*
 * TC2: Check CPU range encoding boundaries.
 *
 * Public APIs tested:
 *   calc_s2_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify exact encodings at the minimum range, an odd remainder, a scale
 *   transition and one table-sized request.
 *
 * Method:
 *   Calculate one chunk for 2, 63, 64 and S2TTES_PER_S2TT granules. Compare
 *   coverage, scale and raw num against fixed expected values.
 *
 * Expected results:
 *   The (coverage, scale, num) tuples are (2, 0, 1), (62, 0, 31), (64, 1, 1)
 *   and (512, 1, 8). The 63-granule input leaves one granule for a later non-
 *   range TLBI.
 */
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

/*
 * TC3: Encode the maximum CPU TLBI range.
 *
 * Public APIs tested:
 *   calc_s2_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify that the maximum legal scale and raw count describe the full
 *   maximum request without splitting it.
 *
 * Method:
 *   Derive max_covered from S2_TLBI_RANGE_NUM_MAX, S2_TLBI_RANGE_SCALE_MAX
 *   and the architectural scale multiplier/bias. Pass that exact size to the
 *   helper.
 *
 * Expected results:
 *   The returned coverage equals max_covered, scale equals
 *   S2_TLBI_RANGE_SCALE_MAX and num equals S2_TLBI_RANGE_NUM_MAX.
 */
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

/*
 * TC4: Decompose CPU TLBI requests without gaps or overshoot.
 *
 * Public APIs tested:
 *   calc_s2_tlbi_range() (internal helper).
 *
 * Aim:
 *   Verify progress, legal fields and complete coverage across small inputs,
 *   table/block boundaries and a request beyond the largest single
 *   instruction.
 *
 * Method:
 *   Iterate the helper for every total from 1 through 4096 and the explicit
 *   boundary list. Subtract each chunk; interpret zero coverage only as a
 *   one-granule non-range remainder.
 *
 * Expected results:
 *   Every range chunk obeys the CPU coverage formula and field limits, never
 *   exceeds the remainder, and reduces it to zero. A zero-coverage result
 *   occurs only with exactly one granule remaining.
 */
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

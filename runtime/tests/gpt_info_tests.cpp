/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_features.h>
#include <sizes.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <test_helpers.h>
#include <tracking_region.h>
#include <utils_def.h>
}

/* Exact memory layout reported by Kohei Enju on Linux mailing list on 21 October 2026. */
#define TEST_PAR_BASE		UL(0x800c0000000)
#define TEST_RAM_BASE		UL(0x800dc400000)
#define TEST_RAM_TOP		UL(0x83000000000)
#define TEST_L0GPTSZ		SZ_1G
#define TEST_PAR_TOP		(TEST_PAR_BASE + TEST_L0GPTSZ)
#define TEST_DEV_PAR_BASE	SZ_1G
#define TEST_DEV_BASE		(TEST_DEV_PAR_BASE + TEST_L0GPTSZ - GRANULE_SIZE)

/*
 * DEN0137 2.0-bet3 A2.3.9.1 defines a PAR as the range covered by one
 * L0GPT entry. Platform-reserved means that memory in the PAR is not
 * delegable; B4.5.7 queries the PAR's GPT allocation state.
 * B4.6.29 allows platform or Host allocation
 * for a PAR containing delegable memory. These tests accept either policy
 * while rejecting RESERVED and invalid allocation states for such a PAR.
 *
 * Install the reported memory bank through the real tracking-index code.
 * Neither the GPT handler nor the memory-category lookup is mocked. Only
 * metadata VA is reserved: none of the reported physical addresses is
 * dereferenced or needs backing on the development host. Querying GPT state
 * does not require tracking activation (A2.3.9.1 RYCFKS/XBJLCS).
 *
 * All cases share one synthetic tracking layout in the group's CTest process.
 * They only query it, so no reset is needed between cases. Do not combine this
 * group with tests which boot the normal host platform in the same process.
 */
TEST_GROUP(gpt_info_tests) {

	u_register_t saved_mmfr0;

	TEST_SETUP()
	{
		static unsigned char tracking_data[TRACKING_REGION_DATA_SIZE]
			__aligned(GRANULE_SIZE);
		static const struct plat_memory_bank ram[] = {
			{TEST_RAM_BASE, TEST_RAM_TOP - TEST_RAM_BASE}
		};
		static const struct plat_memory_bank dev[] = {
			{TEST_DEV_BASE, GRANULE_SIZE}
		};

		test_helpers_init();
		test_helpers_expect_assert_fail(false);
		saved_mmfr0 = cached_idreg.id_aa64mmfr0_el1;
		cached_idreg.id_aa64mmfr0_el1 =
			INPLACE(ID_AA64MMFR0_EL1_PARANGE, 5UL);
		CHECK_EQUAL(48U, arch_feat_get_pa_width());
		CHECK_EQUAL(0, tracking_region_indices_init(
			(uintptr_t)tracking_data, sizeof(tracking_data),
			ram, ARRAY_SIZE(ram), dev, ARRAY_SIZE(dev), NULL, 0UL));
	}

	TEST_TEARDOWN()
	{
		cached_idreg.id_aa64mmfr0_el1 = saved_mmfr0;
	}
};

/* Allocation responsibility and L1GPT creation state may vary by platform. */
static void check_delegable_par_state(unsigned long state)
{
	CHECK_TRUE_TEXT((state == RMI_GPT_PAR_PLAT) ||
		       (state == RMI_GPT_PAR_HOST_NOT_CREATED) ||
		       (state == RMI_GPT_PAR_HOST_CREATED),
		       "PAR containing delegable memory is RESERVED or has an invalid state");
}

/*
 * TC1: Report a non-reserved GPT state for a PAR with a hole before RAM.
 *
 * Public APIs tested:
 *   smc_granule_tracking_get(), smc_gpt_info().
 *
 * Aim:
 *   Verify that RAM later in a PAR makes the PAR non-reserved even when its
 *   first granule is a memory hole, as in the reported Linux memory layout.
 *
 * Method:
 *   Check that rounding TEST_RAM_BASE down to a 1GB boundary gives
 *   TEST_PAR_BASE (0x800c0000000). Query tracking from TEST_PAR_BASE and
 *   TEST_RAM_BASE to TEST_PAR_TOP (0x80100000000), then query GPT state for
 *   the complete PAR. Use the group's synthetic RAM bank without activating
 *   tracking.
 *
 * Expected results:
 *   All calls report RMI_SUCCESS. Tracking reports RMI_MEM_CATEGORY_NONE
 *   through TEST_RAM_BASE, then RMI_MEM_CATEGORY_CONVENTIONAL through
 *   TEST_PAR_TOP. GPT progress ends at TEST_PAR_TOP, with allocation state
 *   accepted by check_delegable_par_state().
 */
TEST(gpt_info_tests, hole_before_ram_in_same_par)
{
	struct smc_result res = {};

	UNSIGNED_LONGS_EQUAL(TEST_PAR_BASE,
			    round_down(TEST_RAM_BASE, TEST_L0GPTSZ));
	smc_granule_tracking_get(TEST_PAR_BASE, TEST_PAR_TOP, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(RMI_MEM_CATEGORY_NONE, res.x[1]);
	UNSIGNED_LONGS_EQUAL(TEST_RAM_BASE, res.x[3]);

	res = {};
	smc_granule_tracking_get(TEST_RAM_BASE, TEST_PAR_TOP, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(RMI_MEM_CATEGORY_CONVENTIONAL, res.x[1]);
	UNSIGNED_LONGS_EQUAL(TEST_PAR_TOP, res.x[3]);

	res = {};
	smc_gpt_info(TEST_PAR_BASE, TEST_PAR_TOP, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(TEST_PAR_TOP, res.x[1]);
	check_delegable_par_state(res.x[2]);
}

/*
 * TC2: Query multiple PARs when the first PAR starts with a memory hole.
 *
 * Public APIs tested:
 *   smc_gpt_info().
 *
 * Aim:
 *   Verify that a query spanning the aligned RAM range reports a
 *   non-reserved state and advances by complete PARs despite a leading hole.
 *
 * Method:
 *   Query GPT state from TEST_PAR_BASE to TEST_RAM_TOP using the group's
 *   synthetic RAM bank, which starts at TEST_RAM_BASE inside the first PAR.
 *
 * Expected results:
 *   The call reports RMI_SUCCESS. Progress is aligned to TEST_L0GPTSZ (1GB)
 *   and lies between TEST_PAR_TOP and TEST_RAM_TOP, inclusive. Allocation
 *   state is accepted by check_delegable_par_state().
 */
TEST(gpt_info_tests, multi_par_query_with_leading_hole)
{
	struct smc_result res = {};

	smc_gpt_info(TEST_PAR_BASE, TEST_RAM_TOP, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_TRUE((res.x[1] >= TEST_PAR_TOP) && (res.x[1] <= TEST_RAM_TOP));
	CHECK_TRUE(ALIGNED(res.x[1], TEST_L0GPTSZ));
	check_delegable_par_state(res.x[2]);
}

/*
 * TC3: Report a non-reserved GPT state for a PAR ending in device memory.
 *
 * Public APIs tested:
 *   smc_granule_tracking_get(), smc_gpt_info().
 *
 * Aim:
 *   Verify that a device bank occupying only the final granule makes its
 *   PAR non-reserved despite the preceding memory hole.
 *
 * Method:
 *   Use the group's one-granule device bank at TEST_DEV_BASE. Query tracking
 *   from TEST_DEV_PAR_BASE and TEST_DEV_BASE to TEST_DEV_PAR_BASE +
 *   TEST_L0GPTSZ, then query GPT state for the complete PAR.
 *
 * Expected results:
 *   All calls report RMI_SUCCESS. Tracking reports RMI_MEM_CATEGORY_NONE
 *   through TEST_DEV_BASE, then RMI_MEM_CATEGORY_DEV_NCOH through the PAR
 *   top. GPT progress ends at the PAR top, with allocation state
 *   accepted by check_delegable_par_state().
 */
TEST(gpt_info_tests, hole_before_device_at_par_end)
{
	struct smc_result res = {};
	unsigned long top = TEST_DEV_PAR_BASE + TEST_L0GPTSZ;

	smc_granule_tracking_get(TEST_DEV_PAR_BASE, top, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(RMI_MEM_CATEGORY_NONE, res.x[1]);
	UNSIGNED_LONGS_EQUAL(TEST_DEV_BASE, res.x[3]);

	res = {};
	smc_granule_tracking_get(TEST_DEV_BASE, top, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(RMI_MEM_CATEGORY_DEV_NCOH, res.x[1]);
	UNSIGNED_LONGS_EQUAL(top, res.x[3]);

	res = {};
	smc_gpt_info(TEST_DEV_PAR_BASE, top, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(top, res.x[1]);
	check_delegable_par_state(res.x[2]);
}

/*
 * TC4: Report a non-reserved GPT state for a PAR starting in RAM.
 *
 * Public APIs tested:
 *   smc_gpt_info().
 *
 * Aim:
 *   Verify that a PAR wholly within the synthetic RAM bank reports a
 *   non-reserved allocation state.
 *
 * Method:
 *   Query GPT state from TEST_PAR_TOP to TEST_PAR_TOP + TEST_L0GPTSZ,
 *   covering the PAR immediately after the one containing the RAM start.
 *
 * Expected results:
 *   The call reports RMI_SUCCESS and progress ends at TEST_PAR_TOP +
 *   TEST_L0GPTSZ. Allocation state is accepted by check_delegable_par_state().
 */
TEST(gpt_info_tests, ram_at_par_base)
{
	struct smc_result res = {};

	smc_gpt_info(TEST_PAR_TOP, TEST_PAR_TOP + TEST_L0GPTSZ, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(TEST_PAR_TOP + TEST_L0GPTSZ, res.x[1]);
	check_delegable_par_state(res.x[2]);
}

/*
 * TC5: Report a valid GPT state for a PAR containing only a memory hole.
 *
 * Public APIs tested:
 *   smc_gpt_info().
 *
 * Aim:
 *   Verify that an empty PAR reports a valid allocation state and progress
 *   ends at the query top.
 *
 * Method:
 *   Query GPT state from TEST_PAR_BASE - TEST_L0GPTSZ to TEST_PAR_BASE,
 *   covering the empty PAR immediately before the one containing RAM.
 *
 * Expected results:
 *   The call reports RMI_SUCCESS and progress ends at TEST_PAR_BASE.
 *   Allocation state is RMI_GPT_PAR_RESERVED or a state accepted by
 *   check_delegable_par_state().
 */
TEST(gpt_info_tests, hole_only_par_before_ram)
{
	struct smc_result res = {};

	smc_gpt_info(TEST_PAR_BASE - TEST_L0GPTSZ, TEST_PAR_BASE, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(TEST_PAR_BASE, res.x[1]);
	CHECK_TRUE((res.x[2] == RMI_GPT_PAR_RESERVED) ||
		   (res.x[2] == RMI_GPT_PAR_PLAT) ||
		   (res.x[2] == RMI_GPT_PAR_HOST_NOT_CREATED) ||
		   (res.x[2] == RMI_GPT_PAR_HOST_CREATED));
}

/*
 * TC6: Stop tracking progress at the RAM start when querying a memory hole.
 *
 * Public APIs tested:
 *   smc_granule_tracking_get().
 *
 * Aim:
 *   Verify that tracking reports the leading hole as reserved and stops at
 *   the RAM bank boundary even when the query extends through RAM.
 *
 * Method:
 *   Query tracking from TEST_PAR_BASE to TEST_RAM_TOP using the group's
 *   synthetic RAM bank, which starts at TEST_RAM_BASE after the hole.
 *
 * Expected results:
 *   The call reports RMI_SUCCESS, memory category RMI_MEM_CATEGORY_NONE and
 *   tracking state RMI_TRACKING_RESERVED. Progress ends at TEST_RAM_BASE.
 */
TEST(gpt_info_tests, tracking_get_stops_at_ram_start)
{
	struct smc_result res = {};

	smc_granule_tracking_get(TEST_PAR_BASE, TEST_RAM_TOP, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(RMI_MEM_CATEGORY_NONE, res.x[1]);
	UNSIGNED_LONGS_EQUAL(RMI_TRACKING_RESERVED, res.x[2]);
	UNSIGNED_LONGS_EQUAL(TEST_RAM_BASE, res.x[3]);
}

/*
 * TC7: Stop tracking progress at the RAM end before reporting the next hole.
 *
 * Public APIs tested:
 *   smc_granule_tracking_get().
 *
 * Aim:
 *   Verify that tracking stops at the RAM bank end and a subsequent query
 *   reports the following memory hole.
 *
 * Method:
 *   Query tracking from TEST_RAM_TOP - GRANULE_SIZE to TEST_RAM_TOP +
 *   GRANULE_SIZE, spanning the last RAM granule and first hole granule.
 *   Query again from TEST_RAM_TOP with the same top.
 *
 * Expected results:
 *   Both calls report RMI_SUCCESS. The first reports memory category
 *   RMI_MEM_CATEGORY_CONVENTIONAL with progress ending at TEST_RAM_TOP.
 *   The second reports RMI_MEM_CATEGORY_NONE with progress ending at
 *   TEST_RAM_TOP + GRANULE_SIZE.
 */
TEST(gpt_info_tests, tracking_get_stops_at_ram_end)
{
	struct smc_result res = {};
	unsigned long top = TEST_RAM_TOP + GRANULE_SIZE;

	smc_granule_tracking_get(TEST_RAM_TOP - GRANULE_SIZE, top, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(RMI_MEM_CATEGORY_CONVENTIONAL, res.x[1]);
	UNSIGNED_LONGS_EQUAL(TEST_RAM_TOP, res.x[3]);

	res = {};
	smc_granule_tracking_get(TEST_RAM_TOP, top, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(RMI_MEM_CATEGORY_NONE, res.x[1]);
	UNSIGNED_LONGS_EQUAL(top, res.x[3]);
}

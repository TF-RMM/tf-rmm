/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <granule.h>
#include <host_utils.h>
#include <string.h>
#include <test_helpers.h>
#include <vdev_test.h>
}

static inline uintptr_t granule_addr_from_idx(unsigned int idx)
{
	return host_util_get_granule_base() + ((uintptr_t)idx * GRANULE_SIZE);
}

static void get_contiguous_rand_granule_array(uintptr_t *arr, unsigned int count)
{
	uintptr_t granule_base = host_util_get_granule_base();
	unsigned long nr_granules = test_helpers_get_nr_granules();
	unsigned long max_start_granule;
	unsigned long start_granule;

	assert(count <= nr_granules);

	max_start_granule = nr_granules - count;
	start_granule = test_helpers_get_rand_in_range(0UL, max_start_granule);

	for (unsigned int i = 0U; i < count; i++) {
		arr[i] = granule_base + ((start_granule + i) * GRANULE_SIZE);
	}
}

static bool buffer_is_zeroed(const void *buf, size_t size)
{
	const unsigned char *bytes = (const unsigned char *)buf;

	for (size_t i = 0U; i < size; ++i) {
		if (bytes[i] != 0U) {
			return false;
		}
	}

	return true;
}

static void setup_test_pdev(struct pdev *pd,
			    uintptr_t *range_page_addrs,
			    unsigned int num_range_pages,
			    uint32_t max_num_vdevs)
{
	(void)memset(pd, 0, sizeof(*pd));
	pd->max_num_vdevs = max_num_vdevs;

	for (unsigned int i = 0U; i < num_range_pages; ++i) {
		(void)memset((void *)range_page_addrs[i], 0, GRANULE_SIZE);
		pd->g_vdevs_ranges_aux[i] = addr_to_granule(range_page_addrs[i]);
	}
}

/*
 * Tests for vdev range slot management across auxiliary granule pages.
 *
 * Virtual device (vdev) address ranges are stored in pdev_vdev_range_slot
 * structures packed into auxiliary granule pages (g_vdevs_ranges_aux).
 * Each granule page holds VDEV_RANGE_SLOTS_PER_GRANULE slots. When more
 * vdevs are configured than fit in a single page, slots spill over into
 * subsequent pages. These tests verify that set, clear, find-free, and
 * overlap-detection operations work correctly across page boundaries.
 */
TEST_GROUP(vdev_range_slot_tests) {
	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start(true);
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
	}

	TEST_TEARDOWN()
	{
		(void)memset((void *)test_helpers_granule_struct_base(), 0,
			     sizeof(struct granule) * test_helpers_get_nr_granules());
	}
};

/*
 * Verify that setting and clearing a vdev range slot that resides on the
 * second auxiliary granule page works correctly.
 *
 * Setup: Two auxiliary pages with max_num_vdevs = VDEV_RANGE_SLOTS_PER_GRANULE + 1,
 * so slot index VDEV_RANGE_SLOTS_PER_GRANULE maps to the first entry on page 1.
 *
 * After set:
 *  - The first page must remain untouched (all zeros).
 *  - The target slot on page 1 must be marked active with the correct
 *    address range and count.
 *  - The is_active query must return true for the slot index.
 *
 * After clear:
 *  - The slot must be zeroed out and is_active must return false.
 */
TEST(vdev_range_slot_tests, set_clear_slot_on_second_range_page)
{
	struct pdev pd;
	uintptr_t page_addrs[2];
	struct rmi_address_range addr_range = {
		.base = granule_addr_from_idx(10U),
		.top = granule_addr_from_idx(11U)
	};
	struct pdev_vdev_range_slot *page0_slots;
	struct pdev_vdev_range_slot *page1_slots;
	const uint32_t slot_idx = (uint32_t)VDEV_RANGE_SLOTS_PER_GRANULE;

	get_contiguous_rand_granule_array(page_addrs, ARRAY_SIZE(page_addrs));
	setup_test_pdev(&pd, page_addrs, ARRAY_SIZE(page_addrs),
			(uint32_t)VDEV_RANGE_SLOTS_PER_GRANULE + 1U);

	vdev_test_pdev_set_vdev_ranges(&pd, slot_idx, &addr_range, 1UL);

	page0_slots = (struct pdev_vdev_range_slot *)page_addrs[0];
	page1_slots = (struct pdev_vdev_range_slot *)page_addrs[1];

	CHECK_TRUE(buffer_is_zeroed(page0_slots, GRANULE_SIZE));
	CHECK_TRUE(page1_slots[0].active);
	LONGS_EQUAL(1UL, page1_slots[0].num_addr_range);
	UNSIGNED_LONGS_EQUAL(addr_range.base, page1_slots[0].addr_range[0].base);
	UNSIGNED_LONGS_EQUAL(addr_range.top, page1_slots[0].addr_range[0].top);
	CHECK_TRUE(vdev_test_pdev_vdev_range_slot_is_active(&pd, slot_idx));

	vdev_test_pdev_clear_vdev_ranges(&pd, slot_idx);

	CHECK_TRUE(buffer_is_zeroed(page1_slots, sizeof(page1_slots[0])));
	CHECK_FALSE(vdev_test_pdev_vdev_range_slot_is_active(&pd, slot_idx));
}

/*
 * Verify that find_free_vdev_slot correctly locates the first inactive slot
 * when the search must cross a page boundary.
 *
 * Setup: Two auxiliary pages with max_num_vdevs = VDEV_RANGE_SLOTS_PER_GRANULE + 2.
 * All slots on page 0 and the first slot on page 1 are marked active,
 * leaving only the second slot on page 1 (global index
 * VDEV_RANGE_SLOTS_PER_GRANULE + 1) free.
 *
 * Expected: The returned free slot index equals VDEV_RANGE_SLOTS_PER_GRANULE + 1.
 */
TEST(vdev_range_slot_tests, find_free_slot_across_range_pages)
{
	struct pdev pd;
	uintptr_t page_addrs[2];
	struct pdev_vdev_range_slot *page0_slots;
	struct pdev_vdev_range_slot *page1_slots;
	uint32_t free_slot;

	get_contiguous_rand_granule_array(page_addrs, ARRAY_SIZE(page_addrs));
	setup_test_pdev(&pd, page_addrs, ARRAY_SIZE(page_addrs),
			(uint32_t)VDEV_RANGE_SLOTS_PER_GRANULE + 2U);

	page0_slots = (struct pdev_vdev_range_slot *)page_addrs[0];
	page1_slots = (struct pdev_vdev_range_slot *)page_addrs[1];

	for (size_t i = 0U; i < (size_t)VDEV_RANGE_SLOTS_PER_GRANULE; ++i) {
		page0_slots[i].active = true;
	}
	page1_slots[0].active = true;

	free_slot = vdev_test_pdev_find_free_vdev_slot(&pd);

	LONGS_EQUAL((long)VDEV_RANGE_SLOTS_PER_GRANULE + 1L, (long)free_slot);
}

/*
 * Verify that overlap detection considers vdev ranges stored on the second
 * auxiliary granule page.
 *
 * Setup: A range [granule 20, granule 22) is installed in the first slot of
 * page 1 (global index VDEV_RANGE_SLOTS_PER_GRANULE).
 *
 * Cases:
 *  - A range [granule 21, granule 23) overlaps the existing range → returns true.
 *  - A range [granule 23, granule 24) is disjoint → returns false.
 */
TEST(vdev_range_slot_tests, overlap_detection_on_second_range_page)
{
	struct pdev pd;
	uintptr_t page_addrs[2];
	struct rmi_address_range existing_range = {
		.base = granule_addr_from_idx(20U),
		.top = granule_addr_from_idx(22U)
	};
	struct rmi_address_range overlapping_range = {
		.base = granule_addr_from_idx(21U),
		.top = granule_addr_from_idx(23U)
	};
	struct rmi_address_range disjoint_range = {
		.base = granule_addr_from_idx(23U),
		.top = granule_addr_from_idx(24U)
	};

	get_contiguous_rand_granule_array(page_addrs, ARRAY_SIZE(page_addrs));
	setup_test_pdev(&pd, page_addrs, ARRAY_SIZE(page_addrs),
			(uint32_t)VDEV_RANGE_SLOTS_PER_GRANULE + 1U);

	vdev_test_pdev_set_vdev_ranges(&pd, (uint32_t)VDEV_RANGE_SLOTS_PER_GRANULE,
				       &existing_range, 1UL);

	CHECK_TRUE(vdev_test_pdev_vdev_ranges_overlap(&pd, &overlapping_range, 1UL));
	CHECK_FALSE(vdev_test_pdev_vdev_ranges_overlap(&pd, &disjoint_range, 1UL));
}

/*
 * Verify basic set/get/clear lifecycle on the first slot of the first page.
 *
 * This is the simplest single-page scenario: one auxiliary page, one vdev
 * slot. Ensures the round-trip set → is_active → clear → !is_active works
 * and that the slot contents are correct after set and zeroed after clear.
 */
TEST(vdev_range_slot_tests, set_clear_slot_on_first_page)
{
	struct pdev pd;
	uintptr_t page_addrs[1];
	struct rmi_address_range addr_range = {
		.base = granule_addr_from_idx(5U),
		.top = granule_addr_from_idx(8U)
	};
	struct pdev_vdev_range_slot *page0_slots;

	get_contiguous_rand_granule_array(page_addrs, ARRAY_SIZE(page_addrs));
	setup_test_pdev(&pd, page_addrs, ARRAY_SIZE(page_addrs), 1U);

	CHECK_FALSE(vdev_test_pdev_vdev_range_slot_is_active(&pd, 0U));

	vdev_test_pdev_set_vdev_ranges(&pd, 0U, &addr_range, 1UL);

	page0_slots = (struct pdev_vdev_range_slot *)page_addrs[0];
	CHECK_TRUE(page0_slots[0].active);
	LONGS_EQUAL(1UL, page0_slots[0].num_addr_range);
	UNSIGNED_LONGS_EQUAL(addr_range.base, page0_slots[0].addr_range[0].base);
	UNSIGNED_LONGS_EQUAL(addr_range.top, page0_slots[0].addr_range[0].top);
	CHECK_TRUE(vdev_test_pdev_vdev_range_slot_is_active(&pd, 0U));

	vdev_test_pdev_clear_vdev_ranges(&pd, 0U);

	CHECK_TRUE(buffer_is_zeroed(&page0_slots[0], sizeof(page0_slots[0])));
	CHECK_FALSE(vdev_test_pdev_vdev_range_slot_is_active(&pd, 0U));
}

/*
 * Verify that setting a slot with multiple address ranges stores all of them.
 *
 * Populates slot 0 with two sorted, non-overlapping address ranges and
 * checks that both are recorded correctly in the slot's addr_range array.
 */
TEST(vdev_range_slot_tests, set_slot_with_multiple_ranges)
{
	struct pdev pd;
	uintptr_t page_addrs[1];
	struct rmi_address_range ranges[2] = {
		{ .base = granule_addr_from_idx(10U),
		  .top = granule_addr_from_idx(12U) },
		{ .base = granule_addr_from_idx(20U),
		  .top = granule_addr_from_idx(25U) }
	};
	struct pdev_vdev_range_slot *page0_slots;

	get_contiguous_rand_granule_array(page_addrs, ARRAY_SIZE(page_addrs));
	setup_test_pdev(&pd, page_addrs, ARRAY_SIZE(page_addrs), 1U);

	vdev_test_pdev_set_vdev_ranges(&pd, 0U, ranges, 2UL);

	page0_slots = (struct pdev_vdev_range_slot *)page_addrs[0];
	CHECK_TRUE(page0_slots[0].active);
	LONGS_EQUAL(2UL, page0_slots[0].num_addr_range);
	UNSIGNED_LONGS_EQUAL(ranges[0].base, page0_slots[0].addr_range[0].base);
	UNSIGNED_LONGS_EQUAL(ranges[0].top, page0_slots[0].addr_range[0].top);
	UNSIGNED_LONGS_EQUAL(ranges[1].base, page0_slots[0].addr_range[1].base);
	UNSIGNED_LONGS_EQUAL(ranges[1].top, page0_slots[0].addr_range[1].top);
}

/*
 * Verify that find_free_vdev_slot returns slot 0 when all slots are empty.
 */
TEST(vdev_range_slot_tests, find_free_slot_returns_first_when_all_empty)
{
	struct pdev pd;
	uintptr_t page_addrs[1];
	uint32_t free_slot;

	get_contiguous_rand_granule_array(page_addrs, ARRAY_SIZE(page_addrs));
	setup_test_pdev(&pd, page_addrs, ARRAY_SIZE(page_addrs),
			(uint32_t)VDEV_RANGE_SLOTS_PER_GRANULE);

	free_slot = vdev_test_pdev_find_free_vdev_slot(&pd);

	LONGS_EQUAL(0L, (long)free_slot);
}

/*
 * Verify that find_free_vdev_slot returns PDEV_VDEV_SLOT_INVALID when every
 * slot across all auxiliary pages is occupied.
 */
TEST(vdev_range_slot_tests, find_free_slot_returns_invalid_when_full)
{
	struct pdev pd;
	uintptr_t page_addrs[1];
	struct pdev_vdev_range_slot *page0_slots;
	uint32_t free_slot;

	get_contiguous_rand_granule_array(page_addrs, ARRAY_SIZE(page_addrs));
	setup_test_pdev(&pd, page_addrs, ARRAY_SIZE(page_addrs),
			(uint32_t)VDEV_RANGE_SLOTS_PER_GRANULE);

	page0_slots = (struct pdev_vdev_range_slot *)page_addrs[0];
	for (size_t i = 0U; i < (size_t)VDEV_RANGE_SLOTS_PER_GRANULE; ++i) {
		page0_slots[i].active = true;
	}

	free_slot = vdev_test_pdev_find_free_vdev_slot(&pd);

	LONGS_EQUAL((long)PDEV_VDEV_SLOT_INVALID, (long)free_slot);
}

/*
 * Verify that find_free_vdev_slot returns the correct slot index when a
 * slot in the middle of the first page is freed.
 *
 * Fill all slots, then deactivate slot at index VDEV_RANGE_SLOTS_PER_GRANULE/2.
 * The search must skip all earlier active slots and return the freed one.
 */
TEST(vdev_range_slot_tests, find_free_slot_returns_gap_in_middle)
{
	struct pdev pd;
	uintptr_t page_addrs[1];
	struct pdev_vdev_range_slot *page0_slots;
	uint32_t free_slot;
	const size_t gap_idx = (size_t)VDEV_RANGE_SLOTS_PER_GRANULE / 2U;

	get_contiguous_rand_granule_array(page_addrs, ARRAY_SIZE(page_addrs));
	setup_test_pdev(&pd, page_addrs, ARRAY_SIZE(page_addrs),
			(uint32_t)VDEV_RANGE_SLOTS_PER_GRANULE);

	page0_slots = (struct pdev_vdev_range_slot *)page_addrs[0];
	for (size_t i = 0U; i < (size_t)VDEV_RANGE_SLOTS_PER_GRANULE; ++i) {
		page0_slots[i].active = true;
	}
	page0_slots[gap_idx].active = false;

	free_slot = vdev_test_pdev_find_free_vdev_slot(&pd);

	LONGS_EQUAL((long)gap_idx, (long)free_slot);
}

/*
 * Verify that overlap detection returns false when no slots are active.
 *
 * An empty pdev (no vdevs installed) must never report overlap with any
 * queried range.
 */
TEST(vdev_range_slot_tests, no_overlap_when_no_active_slots)
{
	struct pdev pd;
	uintptr_t page_addrs[1];
	struct rmi_address_range query = {
		.base = granule_addr_from_idx(0U),
		.top = granule_addr_from_idx(100U)
	};

	get_contiguous_rand_granule_array(page_addrs, ARRAY_SIZE(page_addrs));
	setup_test_pdev(&pd, page_addrs, ARRAY_SIZE(page_addrs),
			(uint32_t)VDEV_RANGE_SLOTS_PER_GRANULE);

	CHECK_FALSE(vdev_test_pdev_vdev_ranges_overlap(&pd, &query, 1UL));
}

/*
 * Verify overlap detection with adjacent (touching) ranges.
 *
 * Two ranges [A, B) and [B, C) where B is both the top of the first and the
 * base of the second are NOT overlapping — the top is exclusive. This is an
 * important boundary condition for the sorted-range overlap algorithm.
 */
TEST(vdev_range_slot_tests, no_overlap_for_adjacent_ranges)
{
	struct pdev pd;
	uintptr_t page_addrs[1];
	struct rmi_address_range existing = {
		.base = granule_addr_from_idx(10U),
		.top = granule_addr_from_idx(20U)
	};
	struct rmi_address_range adjacent_after = {
		.base = granule_addr_from_idx(20U),
		.top = granule_addr_from_idx(30U)
	};

	get_contiguous_rand_granule_array(page_addrs, ARRAY_SIZE(page_addrs));
	setup_test_pdev(&pd, page_addrs, ARRAY_SIZE(page_addrs), 1U);

	vdev_test_pdev_set_vdev_ranges(&pd, 0U, &existing, 1UL);

	CHECK_FALSE(vdev_test_pdev_vdev_ranges_overlap(&pd, &adjacent_after, 1UL));
}

/*
 * Verify overlap when the queried range is a strict subset of an existing
 * range, and when the existing range is a strict subset of the query.
 *
 * Both cases must report overlap — containment in either direction counts.
 */
TEST(vdev_range_slot_tests, overlap_subset_and_superset)
{
	struct pdev pd;
	uintptr_t page_addrs[1];
	struct rmi_address_range existing = {
		.base = granule_addr_from_idx(10U),
		.top = granule_addr_from_idx(20U)
	};
	struct rmi_address_range subset = {
		.base = granule_addr_from_idx(12U),
		.top = granule_addr_from_idx(15U)
	};
	struct rmi_address_range superset = {
		.base = granule_addr_from_idx(5U),
		.top = granule_addr_from_idx(25U)
	};

	get_contiguous_rand_granule_array(page_addrs, ARRAY_SIZE(page_addrs));
	setup_test_pdev(&pd, page_addrs, ARRAY_SIZE(page_addrs), 1U);

	vdev_test_pdev_set_vdev_ranges(&pd, 0U, &existing, 1UL);

	CHECK_TRUE(vdev_test_pdev_vdev_ranges_overlap(&pd, &subset, 1UL));
	CHECK_TRUE(vdev_test_pdev_vdev_ranges_overlap(&pd, &superset, 1UL));
}

/*
 * Verify overlap detection across multiple active slots on different pages.
 *
 * Setup: Two pages. Slot 0 on page 0 holds [10, 15). Slot 0 on page 1
 * holds [30, 35). A query range that only overlaps with the page-1 range
 * must still be detected, confirming the scan covers all pages.
 */
TEST(vdev_range_slot_tests, overlap_spans_multiple_active_slots)
{
	struct pdev pd;
	uintptr_t page_addrs[2];
	struct rmi_address_range range_page0 = {
		.base = granule_addr_from_idx(10U),
		.top = granule_addr_from_idx(15U)
	};
	struct rmi_address_range range_page1 = {
		.base = granule_addr_from_idx(30U),
		.top = granule_addr_from_idx(35U)
	};
	struct rmi_address_range query_hits_page1 = {
		.base = granule_addr_from_idx(32U),
		.top = granule_addr_from_idx(33U)
	};
	struct rmi_address_range query_no_hit = {
		.base = granule_addr_from_idx(20U),
		.top = granule_addr_from_idx(25U)
	};

	get_contiguous_rand_granule_array(page_addrs, ARRAY_SIZE(page_addrs));
	setup_test_pdev(&pd, page_addrs, ARRAY_SIZE(page_addrs),
			(uint32_t)VDEV_RANGE_SLOTS_PER_GRANULE + 1U);

	vdev_test_pdev_set_vdev_ranges(&pd, 0U, &range_page0, 1UL);
	vdev_test_pdev_set_vdev_ranges(&pd, (uint32_t)VDEV_RANGE_SLOTS_PER_GRANULE,
				       &range_page1, 1UL);

	CHECK_TRUE(vdev_test_pdev_vdev_ranges_overlap(&pd, &query_hits_page1, 1UL));
	CHECK_FALSE(vdev_test_pdev_vdev_ranges_overlap(&pd, &query_no_hit, 1UL));
}

/*
 * Verify that clearing a slot does not affect neighbouring slots on the
 * same page.
 *
 * Setup: Three consecutive slots on page 0, each with a distinct range.
 * Clear the middle slot (index 1) and verify that slots 0 and 2 are
 * unchanged and still active.
 */
TEST(vdev_range_slot_tests, clear_does_not_corrupt_adjacent_slots)
{
	struct pdev pd;
	uintptr_t page_addrs[1];
	struct rmi_address_range ranges[3] = {
		{ .base = granule_addr_from_idx(10U),
		  .top = granule_addr_from_idx(12U) },
		{ .base = granule_addr_from_idx(20U),
		  .top = granule_addr_from_idx(22U) },
		{ .base = granule_addr_from_idx(30U),
		  .top = granule_addr_from_idx(32U) }
	};
	struct pdev_vdev_range_slot *page0_slots;

	get_contiguous_rand_granule_array(page_addrs, ARRAY_SIZE(page_addrs));
	setup_test_pdev(&pd, page_addrs, ARRAY_SIZE(page_addrs), 3U);

	for (uint32_t i = 0U; i < 3U; ++i) {
		vdev_test_pdev_set_vdev_ranges(&pd, i, &ranges[i], 1UL);
	}

	vdev_test_pdev_clear_vdev_ranges(&pd, 1U);

	page0_slots = (struct pdev_vdev_range_slot *)page_addrs[0];

	/* Slot 0 intact */
	CHECK_TRUE(page0_slots[0].active);
	UNSIGNED_LONGS_EQUAL(ranges[0].base, page0_slots[0].addr_range[0].base);
	UNSIGNED_LONGS_EQUAL(ranges[0].top, page0_slots[0].addr_range[0].top);

	/* Slot 1 cleared */
	CHECK_FALSE(page0_slots[1].active);
	LONGS_EQUAL(0L, (long)page0_slots[1].num_addr_range);

	/* Slot 2 intact */
	CHECK_TRUE(page0_slots[2].active);
	UNSIGNED_LONGS_EQUAL(ranges[2].base, page0_slots[2].addr_range[0].base);
	UNSIGNED_LONGS_EQUAL(ranges[2].top, page0_slots[2].addr_range[0].top);
}

/*
 * Verify that a cleared slot is not considered during overlap detection.
 *
 * Setup: Install range [10, 20) in slot 0, then clear it. A subsequent
 * overlap query for a range that would have overlapped must return false.
 */
TEST(vdev_range_slot_tests, cleared_slot_not_checked_for_overlap)
{
	struct pdev pd;
	uintptr_t page_addrs[1];
	struct rmi_address_range existing = {
		.base = granule_addr_from_idx(10U),
		.top = granule_addr_from_idx(20U)
	};
	struct rmi_address_range query = {
		.base = granule_addr_from_idx(12U),
		.top = granule_addr_from_idx(15U)
	};

	get_contiguous_rand_granule_array(page_addrs, ARRAY_SIZE(page_addrs));
	setup_test_pdev(&pd, page_addrs, ARRAY_SIZE(page_addrs), 1U);

	vdev_test_pdev_set_vdev_ranges(&pd, 0U, &existing, 1UL);
	CHECK_TRUE(vdev_test_pdev_vdev_ranges_overlap(&pd, &query, 1UL));

	vdev_test_pdev_clear_vdev_ranges(&pd, 0U);
	CHECK_FALSE(vdev_test_pdev_vdev_ranges_overlap(&pd, &query, 1UL));
}

/*
 * Verify that overwriting an already-active slot replaces the old range.
 *
 * Setup: Set slot 0 to [10, 20), then overwrite with [50, 60).
 * The old range must no longer trigger overlap; the new range must.
 */
TEST(vdev_range_slot_tests, overwrite_replaces_existing_range)
{
	struct pdev pd;
	uintptr_t page_addrs[1];
	struct rmi_address_range old_range = {
		.base = granule_addr_from_idx(10U),
		.top = granule_addr_from_idx(20U)
	};
	struct rmi_address_range new_range = {
		.base = granule_addr_from_idx(50U),
		.top = granule_addr_from_idx(60U)
	};
	struct rmi_address_range query_old = {
		.base = granule_addr_from_idx(12U),
		.top = granule_addr_from_idx(15U)
	};
	struct rmi_address_range query_new = {
		.base = granule_addr_from_idx(52U),
		.top = granule_addr_from_idx(55U)
	};

	get_contiguous_rand_granule_array(page_addrs, ARRAY_SIZE(page_addrs));
	setup_test_pdev(&pd, page_addrs, ARRAY_SIZE(page_addrs), 1U);

	vdev_test_pdev_set_vdev_ranges(&pd, 0U, &old_range, 1UL);
	CHECK_TRUE(vdev_test_pdev_vdev_ranges_overlap(&pd, &query_old, 1UL));

	vdev_test_pdev_set_vdev_ranges(&pd, 0U, &new_range, 1UL);
	CHECK_FALSE(vdev_test_pdev_vdev_ranges_overlap(&pd, &query_old, 1UL));
	CHECK_TRUE(vdev_test_pdev_vdev_ranges_overlap(&pd, &query_new, 1UL));
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <dev.h>
#include <granule.h>
#include <host_utils.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <test_helpers.h>

void vdev_test_pdev_set_vdev_ranges(struct pdev *pd, uint32_t slot_idx,
				    const struct rmi_address_range *addr_range,
				    unsigned long addr_range_cnt);
void vdev_test_pdev_clear_vdev_ranges(struct pdev *pd, uint32_t slot_idx);
bool vdev_test_pdev_vdev_range_slot_is_active(const struct pdev *pd,
					      uint32_t slot_idx);
uint32_t vdev_test_pdev_find_free_vdev_slot(const struct pdev *pd);
bool vdev_test_pdev_vdev_ranges_overlap(
	const struct pdev *pd,
	const struct rmi_address_range *addr_range,
	unsigned long addr_range_cnt);
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

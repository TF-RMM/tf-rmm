/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <realm.h>
}

TEST_GROUP(realm_bounds_tests) {
};

/* A valid range includes its base and excludes its end. */
TEST(realm_bounds_tests, addr_is_contained_uses_half_open_bounds)
{
	CHECK_TRUE(addr_is_contained(0x1000UL, 0x2000UL, 0x1000UL));
	CHECK_TRUE(addr_is_contained(0x1000UL, 0x2000UL, 0x1FFFUL));
	CHECK_FALSE(addr_is_contained(0x1000UL, 0x2000UL, 0x2000UL));
}

/* A zero or reversed end does not describe a valid container. */
TEST(realm_bounds_tests, addr_is_contained_rejects_zero_or_reversed_end)
{
	CHECK_FALSE(addr_is_contained(0x1000UL, 0UL, 0x1000UL));
	CHECK_FALSE(addr_is_contained(0x2000UL, 0x1000UL, 0x1800UL));
}

/* Reject empty, reversed, and wrapped regions before checking containment. */
TEST(realm_bounds_tests, region_is_contained_rejects_empty_reversed_or_wrapped_range)
{
	CHECK_FALSE(region_is_contained(0x1000UL, 0x3000UL,
					0x2000UL, 0x2000UL));
	CHECK_FALSE(region_is_contained(0x1000UL, 0x3000UL,
					0x2800UL, 0x2000UL));
	CHECK_FALSE(region_is_contained(0UL, 0UL, 0x1000UL, 0UL));
	CHECK_FALSE(region_is_contained(0UL, 0x2000UL, 0x1000UL, 0UL));
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/TestHarness.h>

extern "C" {
#include <vdev_test.h>
}

TEST_GROUP(vdev_stream_range_tests) {
};

/* PDEV stream ranges may be supplied in any order without a coverage gap. */
TEST(vdev_stream_range_tests, reversed_contiguous_ranges_cover_vdev_range)
{
	struct pdev_stream streams[RMI_PDEV_STREAM_TYPE_COUNT] = {};
	struct pdev_stream *ncoh = &streams[RMI_PDEV_STREAM_NCOH];
	struct rmi_address_range vdev_range = {
		.base = 0x1000UL,
		.top = 0x3000UL
	};

	ncoh->taken = true;
	ncoh->num_addr_range = 2UL;
	ncoh->addr_range[0].base = 0x2000UL;
	ncoh->addr_range[0].top = 0x3000UL;
	ncoh->addr_range[1].base = 0x1000UL;
	ncoh->addr_range[1].top = 0x2000UL;

	CHECK_TRUE(vdev_test_addr_ranges_in_pdev_streams(&streams, &vdev_range, 1UL));

	/* A real gap must still fail the coverage check. */
	ncoh->addr_range[1].top = 0x1800UL;
	CHECK_FALSE(vdev_test_addr_ranges_in_pdev_streams(&streams, &vdev_range, 1UL));
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>
#include <s2tt_tests_base_g1.h>

extern "C" {
#include <test_helpers.h>
#include <s2tt_test_helpers.h>
}

TEST_GROUP(s2tt_non_lpa2) {
	TEST_SETUP()
	{
		s2tt_test_helpers_setup(LPA2_DISABLED);
	}

	TEST_TEARDOWN()
	{}
};

TEST(s2tt_non_lpa2, s2tte_create_unassigned_empty_tc1)
{
	s2tte_create_unassigned_empty_tc1();
}

TEST(s2tt_non_lpa2, s2tte_create_unassigned_ram_tc1)
{
	s2tte_create_unassigned_ram_tc1();
}

TEST(s2tt_non_lpa2, s2tte_create_unassigned_destroyed_tc1)
{
	s2tte_create_unassigned_destroyed_tc1();
}

TEST(s2tt_non_lpa2, s2tte_create_unassigned_ns_tc1)
{
	s2tte_create_unassigned_ns_tc1();
}

TEST(s2tt_non_lpa2, s2tte_create_assigned_destroyed_tc1)
{
	s2tte_create_assigned_destroyed_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_destroyed_tc2)
{
	s2tte_create_assigned_destroyed_tc2();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_destroyed_tc3)
{
	s2tte_create_assigned_destroyed_tc3();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_destroyed_tc4)
{
	s2tte_create_assigned_destroyed_tc4();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_destroyed_tc5)
{
	s2tte_create_assigned_destroyed_tc5();
}

TEST(s2tt_non_lpa2, s2tte_create_assigned_empty_tc1)
{
	s2tte_create_assigned_empty_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_empty_tc2)
{
	s2tte_create_assigned_empty_tc2();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_empty_tc3)
{
	s2tte_create_assigned_empty_tc3();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_empty_tc4)
{
	s2tte_create_assigned_empty_tc4();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_empty_tc5)
{
	s2tte_create_assigned_empty_tc5();
}

TEST(s2tt_non_lpa2, s2tte_create_assigned_ram_tc1)
{
	s2tte_create_assigned_ram_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_ram_tc2)
{
	s2tte_create_assigned_ram_tc2();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_ram_tc3)
{
	s2tte_create_assigned_ram_tc3();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_ram_tc4)
{
	s2tte_create_assigned_ram_tc4();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_ram_tc5)
{
	s2tte_create_assigned_ram_tc5();
}

TEST(s2tt_non_lpa2, s2tte_create_assigned_ns_tc1)
{
	s2tte_create_assigned_ns_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_ns_tc2)
{
	s2tte_create_assigned_ns_tc2();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_ns_tc3)
{
	s2tte_create_assigned_ns_tc3();
}

TEST(s2tt_non_lpa2, s2tte_create_assigned_unchanged_tc1)
{
	s2tte_create_assigned_unchanged_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_unchanged_tc2)
{
	s2tte_create_assigned_unchanged_tc2();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_unchanged_tc3)
{
	s2tte_create_assigned_unchanged_tc3();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_unchanged_tc4)
{
	s2tte_create_assigned_unchanged_tc4();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_unchanged_tc5)
{
	s2tte_create_assigned_unchanged_tc5();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_assigned_unchanged_tc6)
{
	s2tte_create_assigned_unchanged_tc6();
}

TEST(s2tt_non_lpa2, s2tte_create_table_tc1)
{
	s2tte_create_table_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_table_tc2)
{
	s2tte_create_table_tc2();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_table_tc3)
{
	s2tte_create_table_tc3();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_table_tc4)
{
	s2tte_create_table_tc4();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_create_table_tc5)
{
	s2tte_create_table_tc5();
}

TEST(s2tt_non_lpa2, host_ns_s2tte_is_valid_tc1)
{
	host_ns_s2tte_is_valid_tc1();
}

TEST(s2tt_non_lpa2, host_ns_s2tte_is_valid_tc2)
{
	host_ns_s2tte_is_valid_tc2();
}

ASSERT_TEST(s2tt_non_lpa2, host_ns_s2tte_is_valid_tc3)
{
	host_ns_s2tte_is_valid_tc3();
}

ASSERT_TEST(s2tt_non_lpa2, host_ns_s2tte_is_valid_tc4)
{
	host_ns_s2tte_is_valid_tc4();
}

ASSERT_TEST(s2tt_non_lpa2, host_ns_s2tte_is_valid_tc5)
{
	host_ns_s2tte_is_valid_tc5();
}

TEST(s2tt_non_lpa2, host_ns_s2tte_tc1)
{
	host_ns_s2tte_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, host_ns_s2tte_tc2)
{
	host_ns_s2tte_tc2();
}

ASSERT_TEST(s2tt_non_lpa2, host_ns_s2tte_tc3)
{
	host_ns_s2tte_tc3();
}

ASSERT_TEST(s2tt_non_lpa2, host_ns_s2tte_tc4)
{
	host_ns_s2tte_tc4();
}

TEST(s2tt_non_lpa2, s2tte_has_ripas_tc1)
{
	s2tte_has_ripas_tc1();
}

TEST(s2tt_non_lpa2, s2tte_has_ripas_tc2)
{
	s2tte_has_ripas_tc2();
}

TEST(s2tt_non_lpa2, s2tte_is_unassigned_tc1)
{
	s2tte_is_unassigned_tc1();
}

TEST(s2tt_non_lpa2, s2tte_is_unassigned_empty_tc1)
{
	s2tte_is_unassigned_empty_tc1();
}

TEST(s2tt_non_lpa2, s2tte_is_unassigned_ram_tc1)
{
	s2tte_is_unassigned_ram_tc1();
}

TEST(s2tt_non_lpa2, s2tte_is_unassigned_ns_tc1)
{
	s2tte_is_unassigned_ns_tc1();
}

TEST(s2tt_non_lpa2, s2tte_is_unassigned_destroyed_tc1)
{
	s2tte_is_unassigned_destroyed_tc1();
}

TEST(s2tt_non_lpa2, s2tte_is_assigned_empty_tc1)
{
	s2tte_is_assigned_empty_tc1();
}

TEST(s2tt_non_lpa2, s2tte_is_assigned_ns_tc1)
{
	s2tte_is_assigned_ns_tc1();
}

TEST(s2tt_non_lpa2, s2tte_is_assigned_ns_tc2)
{
	s2tte_is_assigned_ns_tc2();
}

TEST(s2tt_non_lpa2, s2tte_is_assigned_ram_tc1)
{
	s2tte_is_assigned_ram_tc1();
}

TEST(s2tt_non_lpa2, s2tte_is_assigned_ram_tc2)
{
	s2tte_is_assigned_ram_tc2();
}

TEST(s2tt_non_lpa2, s2tte_is_assigned_destroyed_tc1)
{
	s2tte_is_assigned_destroyed_tc1();
}

TEST(s2tt_non_lpa2, s2tte_is_table_tc1)
{
	s2tte_is_table_tc1();
}

TEST(s2tt_non_lpa2, s2tte_get_ripas_tc1)
{
	s2tte_get_ripas_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_get_ripas_tc2)
{
	s2tte_get_ripas_tc2();
}

TEST(s2tt_non_lpa2, s2tt_init_unassigned_empty_tc1)
{
	s2tt_init_unassigned_empty_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_unassigned_empty_tc2)
{
	s2tt_init_unassigned_empty_tc2();
}

TEST(s2tt_non_lpa2, s2tt_init_unassigned_ram_tc1)
{
	s2tt_init_unassigned_ram_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_unassigned_ram_tc2)
{
	s2tt_init_unassigned_ram_tc2();
}

TEST(s2tt_non_lpa2, s2tt_init_unassigned_ns_tc1)
{
	s2tt_init_unassigned_ns_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_unassigned_ns_tc2)
{
	s2tt_init_unassigned_ns_tc2();
}

TEST(s2tt_non_lpa2, s2tt_init_unassigned_destroyed_tc1)
{
	s2tt_init_unassigned_destroyed_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_unassigned_destroyed_tc2)
{
	s2tt_init_unassigned_destroyed_tc2();
}

TEST(s2tt_non_lpa2, s2tt_init_assigned_empty_tc1)
{
	s2tt_init_assigned_empty_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_empty_tc2)
{
	s2tt_init_assigned_empty_tc2();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_empty_tc3)
{
	s2tt_init_assigned_empty_tc3();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_empty_tc4)
{
	s2tt_init_assigned_empty_tc4();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_empty_tc5)
{
	s2tt_init_assigned_empty_tc5();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_empty_tc6)
{
	s2tt_init_assigned_empty_tc6();
}

TEST(s2tt_non_lpa2, s2tt_init_assigned_ram_tc1)
{
	s2tt_init_assigned_ram_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_ram_tc2)
{
	s2tt_init_assigned_ram_tc2();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_ram_tc3)
{
	s2tt_init_assigned_ram_tc3();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_ram_tc4)
{
	s2tt_init_assigned_ram_tc4();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_ram_tc5)
{
	s2tt_init_assigned_ram_tc5();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_ram_tc6)
{
	s2tt_init_assigned_ram_tc6();
}

TEST(s2tt_non_lpa2, s2tt_init_assigned_ns_tc1)
{
	s2tt_init_assigned_ns_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_ns_tc2)
{
	s2tt_init_assigned_ns_tc2();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_ns_tc3)
{
	s2tt_init_assigned_ns_tc3();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_ns_tc4)
{
	s2tt_init_assigned_ns_tc4();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_ns_tc5)
{
	s2tt_init_assigned_ns_tc5();
}

TEST(s2tt_non_lpa2, s2tt_init_assigned_destroyed_tc1)
{
	s2tt_init_assigned_destroyed_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_destroyed_tc2)
{
	s2tt_init_assigned_destroyed_tc2();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_destroyed_tc3)
{
	s2tt_init_assigned_destroyed_tc3();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_destroyed_tc4)
{
	s2tt_init_assigned_destroyed_tc4();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_destroyed_tc5)
{
	s2tt_init_assigned_destroyed_tc5();
}

ASSERT_TEST(s2tt_non_lpa2, s2tt_init_assigned_destroyed_tc6)
{
	s2tt_init_assigned_destroyed_tc6();
}

TEST(s2tt_non_lpa2, s2tte_pa_tc1)
{
	s2tte_pa_tc1();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_pa_tc2)
{
	s2tte_pa_tc2();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_pa_tc3)
{
	s2tte_pa_tc3();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_pa_tc4)
{
	s2tte_pa_tc4();
}

ASSERT_TEST(s2tt_non_lpa2, s2tte_pa_tc5)
{
	s2tte_pa_tc5();
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>
#include <xlat_tests_base.h>

extern "C" {
#include <test_helpers.h>
#include <xlat_test_helpers.h>
}

TEST_GROUP(xlat_tests_no_LPA2) {
	TEST_SETUP()
	{
		xlat_test_setup(LPA2_DISABLED);
	}

	TEST_TEARDOWN()
	{}
};

TEST(xlat_tests_no_LPA2, map_region_full_spec_TC1)
{
	map_region_full_spec_tc1();
}

TEST(xlat_tests_no_LPA2, map_region_TC1)
{
	map_region_tc1();
}

TEST(xlat_tests_no_LPA2, map_region_flat_TC1)
{
	map_region_flat_tc1();
}

TEST(xlat_tests_no_LPA2, map_region_transient_TC1)
{
	map_region_transient_tc1();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_cfg_init_TC1)
{
	xlat_ctx_cfg_init_tc1();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_cfg_init_TC2)
{
	xlat_ctx_cfg_init_tc2();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_cfg_init_TC3)
{
	xlat_ctx_cfg_init_tc3();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_cfg_init_TC4)
{
	xlat_ctx_cfg_init_tc4();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_cfg_init_TC5)
{
	xlat_ctx_cfg_init_tc5();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_cfg_init_TC6)
{
	xlat_ctx_cfg_init_tc6();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_cfg_init_TC7)
{
	xlat_ctx_cfg_init_tc7();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_cfg_init_TC8)
{
	xlat_ctx_cfg_init_tc8();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_cfg_init_TC9)
{
	xlat_ctx_cfg_init_tc9();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_cfg_init_TC10)
{
	xlat_ctx_cfg_init_tc10();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_cfg_init_TC11)
{
	xlat_ctx_cfg_init_tc11();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_cfg_init_TC12)
{
	xlat_ctx_cfg_init_tc12();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_cfg_init_TC13)
{
	xlat_ctx_cfg_init_tc13();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_init_TC1)
{
	xlat_ctx_init_tc1();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_init_TC2)
{
	xlat_ctx_init_tc2();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_init_TC3)
{
	xlat_ctx_init_tc3();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_ctx_init_TC4)
{
	xlat_ctx_init_tc4();
}

TEST(xlat_tests_no_LPA2, xlat_ctx_init_TC5)
{
	xlat_ctx_init_tc5();
}

TEST(xlat_tests_no_LPA2, xlat_get_llt_from_va_TC1)
{
	xlat_get_llt_from_va_tc1();
}

TEST(xlat_tests_no_LPA2, xlat_get_llt_from_va_TC2)
{
	xlat_get_llt_from_va_tc2();
}

TEST(xlat_tests_no_LPA2, xlat_get_llt_from_va_TC3)
{
	xlat_get_llt_from_va_tc3();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_get_llt_from_va_TC4)
{
	xlat_get_llt_from_va_tc4();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_get_llt_from_va_TC5)
{
	xlat_get_llt_from_va_tc5();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_get_llt_from_va_TC6)
{
	xlat_get_llt_from_va_tc6();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_get_llt_from_va_TC7)
{
	xlat_get_llt_from_va_tc7();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_get_llt_from_va_TC8)
{
	xlat_get_llt_from_va_tc8();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_get_llt_from_va_TC9)
{
	xlat_get_llt_from_va_tc9();
}

TEST(xlat_tests_no_LPA2, xlat_get_tte_ptr_TC1)
{
	xlat_get_tte_ptr_tc1();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_get_tte_ptr_TC2)
{
	xlat_get_tte_ptr_tc2();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_get_tte_ptr_TC3)
{
	xlat_get_tte_ptr_tc3();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_get_tte_ptr_TC4)
{
	xlat_get_tte_ptr_tc4();
}

TEST(xlat_tests_no_LPA2, xlat_unmap_memory_page_TC1)
{
	xlat_unmap_memory_page_tc1();
}

TEST(xlat_tests_no_LPA2, xlat_unmap_memory_page_TC2)
{
	xlat_unmap_memory_page_tc2();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_unmap_memory_page_TC3)
{
	xlat_unmap_memory_page_tc3();
}

TEST(xlat_tests_no_LPA2, xlat_map_memory_page_with_attrs_TC1)
{
	xlat_map_memory_page_with_attrs_tc1();
}

TEST(xlat_tests_no_LPA2, xlat_map_memory_page_with_attrs_TC2)
{
	xlat_map_memory_page_with_attrs_tc2();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_map_memory_page_with_attrs_TC3)
{
	xlat_map_memory_page_with_attrs_tc3();
}

TEST(xlat_tests_no_LPA2, xlat_arch_setup_mmu_cfg_TC1)
{
	xlat_arch_setup_mmu_cfg_tc1();
}

TEST(xlat_tests_no_LPA2, xlat_arch_setup_mmu_cfg_TC2)
{
	xlat_arch_setup_mmu_cfg_tc2();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_arch_setup_mmu_cfg_TC3)
{
	xlat_arch_setup_mmu_cfg_tc3();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_arch_setup_mmu_cfg_TC4)
{
	xlat_arch_setup_mmu_cfg_tc4();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_arch_setup_mmu_cfg_TC5)
{
	xlat_arch_setup_mmu_cfg_tc5();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_arch_setup_mmu_cfg_TC6)
{
	xlat_arch_setup_mmu_cfg_tc6();
}

ASSERT_TEST(xlat_tests_no_LPA2, xlat_arch_setup_mmu_cfg_TC7)
{
	xlat_arch_setup_mmu_cfg_tc7();
}

TEST(xlat_tests_no_LPA2, xlat_get_oa_from_tte_TC1)
{
	xlat_get_oa_from_tte_tc1();
}

IGNORE_TEST(xlat_tests_no_LPA2, xlat_write_tte_TC1)
{
	/*
	 * xlat_write_tte() is implemented as an assembler function
	 * for target AArch64 Architecture. There is a C stub for the
	 * fake_host platform which we do not need to test.
	 *
	 * This test can therefore be ignored.
	 */

	TEST_EXIT;
}

IGNORE_TEST(xlat_tests_no_LPA2, xlat_read_tte_TC1)
{
	/*
	 * xlat_read_tte() is implemented as an assembler function
	 * for target AArch64 Architecture. There is a C stub for the
	 * fake_host platform which we do not need to test.
	 *
	 * This test can therefore be ignored.
	 */

	TEST_EXIT;
}

IGNORE_TEST(xlat_tests_no_LPA2, xlat_enable_mmu_el2_TC1)
{
	/*
	 * xlat_enable_mmu_el2() is implemented as an assembler function
	 * for target AArch64 Architecture. There is a C stub for the
	 * fake_host platform which we do not need to test.
	 *
	 * This test can therefore be ignored.
	 */

	TEST_EXIT;
}

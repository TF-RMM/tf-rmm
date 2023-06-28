#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

if(RMM_UNITTESTS)
        target_include_directories(rmm-lib-xlat
            PRIVATE "tests")

        target_sources(rmm-lib-xlat
                PRIVATE "tests/xlat_tests_base_g1.cpp"
                        "tests/xlat_tests_base_g2.cpp"
                        "tests/xlat_test_helpers.c")
endif()

# Add test functionality
rmm_build_unittest(NAME xlat_tests_LPA2
                   LIBRARIES rmm-platform
                   TARGET rmm-lib-xlat
                   SOURCES "tests/xlat_tests_lpa2.cpp"
                   ITERATIONS 10)

rmm_build_unittest(NAME xlat_tests_no_LPA2
                   LIBRARIES rmm-platform
                   TARGET rmm-lib-xlat
                   SOURCES "tests/xlat_tests_no_lpa2.cpp"
                   ITERATIONS 10)

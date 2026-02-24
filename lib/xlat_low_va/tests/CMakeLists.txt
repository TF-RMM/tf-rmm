#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

if(RMM_UNITTESTS)
    target_include_directories(rmm-lib-xlat_low_va
        PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/../xlat/src"
                "${CMAKE_CURRENT_SOURCE_DIR}/../xlat/tests"
                "${CMAKE_CURRENT_SOURCE_DIR}/src")
endif()

# Add test functionality
rmm_build_unittest(NAME xlat_low_va
                   TARGET rmm-lib-xlat_low_va
                   LIBRARIES rmm-lib-xlat
                             rmm-platform
                   SOURCES "tests/xlat_low_va_tests.cpp"
                           "tests/xlat_low_va_setup_test.cpp"
                   ITERATIONS 10)
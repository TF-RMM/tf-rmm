#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

if(RMM_UNITTESTS)
    target_include_directories(rmm-lib-mec
        PRIVATE "tests")
endif()

# Add test functionality
rmm_build_unittest(NAME mec
                   TARGET rmm-lib-mec
                   LIBRARIES rmm-platform
                   SOURCES "tests/mec.cpp"
                           "tests/mec_test_helpers.c"
                   ITERATIONS 10)

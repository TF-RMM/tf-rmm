#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

target_include_directories(rmm-lib-realm
    PRIVATE "tests")

# Add test functionality
rmm_build_unittest(NAME granule
                   TARGET rmm-lib-realm
                   SOURCES "tests/granule.cpp"
                           "tests/realm_test_utils.c"
                           "tests/test_harness.c"
                   ITERATIONS 10)

rmm_build_unittest(NAME slot_buffer
                   TARGET rmm-lib-realm
                   SOURCES "tests/buffer.cpp"
                           "tests/realm_test_utils.c"
                           "tests/test_harness.c"
                   ITERATIONS 10)

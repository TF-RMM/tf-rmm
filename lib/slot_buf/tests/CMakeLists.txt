#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

if(RMM_UNITTESTS)
    target_include_directories(rmm-lib-slot_buf
        PRIVATE "tests")
endif()

# Add test functionality
rmm_build_unittest(NAME slot_buffer
                   TARGET rmm-lib-slot_buf
                   SOURCES "tests/buffer.cpp"
                           "tests/buffer_test_helpers.c"
                   ITERATIONS 10)

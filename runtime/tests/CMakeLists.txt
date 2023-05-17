#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

target_include_directories(rmm-runtime
    PRIVATE "tests")

# Add test functionality
rmm_build_unittest(NAME rsi_logger_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/rsi_logger_tests.cpp"
                   ITERATIONS 10)

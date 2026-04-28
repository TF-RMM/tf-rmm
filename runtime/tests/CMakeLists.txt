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

rmm_build_unittest(NAME rec_sro_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/rec_sro_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME sro_donate_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/sro_donate_tests.cpp"
                   ITERATIONS 1)

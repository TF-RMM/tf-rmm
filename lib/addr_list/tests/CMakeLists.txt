#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# Add test functionality
rmm_build_unittest(NAME addr_list_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-lib-addr_list
                   SOURCES "tests/addr_list_tests.cpp"
                   ITERATIONS 10)

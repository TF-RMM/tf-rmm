#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# Add test functionality
rmm_build_unittest(NAME granule
                   TARGET rmm-lib-realm
                   SOURCES "tests/granule.cpp"
                           "tests/test_harness.c"
                   ITERATIONS 10)

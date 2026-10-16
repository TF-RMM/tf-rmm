#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# Add test functionality
rmm_build_unittest(NAME smmuv3_tlbi
                   ADDITIONAL_TEST_GROUPS smmuv3_tlbi_active_psmmu
                                          smmuv3_tlbi_range
                   TARGET rmm-lib-smmuv3
                   LIBRARIES rmm-lib-debug rmm-platform
                   SOURCES "tests/smmuv3_tlbi_tests.cpp"
                           "tests/smmuv3_tlbi_range_tests.cpp"
                   ITERATIONS 1)

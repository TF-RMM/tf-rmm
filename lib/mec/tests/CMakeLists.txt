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
                   ADDITIONAL_TEST_GROUPS no_mec
                                          mec_restore_after_assert1
                                          mec_restore_after_assert2
                                          mec_restore_after_assert3
                                          mec_restore_after_assert4
                                          mec_restore_after_assert5
                                          mec_restore_after_assert6
                                          no_sctlr2_mec
                   SOURCES "tests/mec.cpp"
                           "tests/mec_test_helpers.c"
                   ITERATIONS 1)

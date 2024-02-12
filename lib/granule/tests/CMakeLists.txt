#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

if(RMM_UNITTESTS)
    target_include_directories(rmm-lib-granule
        PRIVATE "tests")
endif()

# Add test functionality
rmm_build_unittest(NAME granule
                   TARGET rmm-lib-granule
                   LIBRARIES rmm-lib-slot_buf
                             rmm-platform
                             rmm-lib-xlat
                   SOURCES "tests/granule.cpp"
                   ITERATIONS 10)


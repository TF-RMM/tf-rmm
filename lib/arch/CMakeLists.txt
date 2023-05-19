#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-arch)

target_link_libraries(rmm-lib-arch
    PRIVATE rmm-lib-common
            rmm-lib-smc)

target_include_directories(rmm-lib-arch
    PUBLIC  "include"
            "include/${RMM_ARCH}"
    PRIVATE "src/${RMM_ARCH}"
            "src/include")

target_sources(rmm-lib-arch
        PRIVATE "src/arch_features.c"
                "src/pmu.c"
                "src/pauth.c"
                "src/simd.c")

if(NOT RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-lib-arch
        PRIVATE "src/aarch64/cache_helpers.S"
                "src/aarch64/simd_helpers.S")
else()
    target_sources(rmm-lib-arch
        PRIVATE "src/fake_host/cache_wrappers.c"
                "src/fake_host/simd_helpers.c")
endif()

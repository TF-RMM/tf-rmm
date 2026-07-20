#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-simd)

target_link_libraries(rmm-lib-simd
    PUBLIC rmm-lib-arch)

target_include_directories(rmm-lib-simd
    PUBLIC "include"
    PRIVATE "src/${RMM_ARCH}"
            "src/include")

if(HOST_VARIANT STREQUAL "host_cbmc")
    target_sources(rmm-lib-simd
        PRIVATE "src/fake_host/cbmc_simd.c")
    return()
endif()

target_sources(rmm-lib-simd
    PRIVATE "src/simd.c")

if(NOT RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-lib-simd
        PRIVATE "src/aarch64/simd_helpers.S")
else()
    target_sources(rmm-lib-simd
        PRIVATE "src/fake_host/simd_helpers.c")
endif()

include(tests/CMakeLists.txt)

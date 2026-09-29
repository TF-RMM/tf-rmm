#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-granule)

target_link_libraries(rmm-lib-granule
    PUBLIC rmm-lib-arch
           rmm-lib-common
    PRIVATE rmm-lib-debug
            rmm-lib-rmm_el3_ifc
            rmm-lib-smc
            rmm-lib-sro_context
            rmm-lib-xlat
            rmm-lib-xlat_low_va)

target_include_directories(rmm-lib-granule
    PUBLIC "include"
           "include/${RMM_ARCH}"
    PRIVATE "src"
            "src/${RMM_ARCH}")

target_sources(rmm-lib-granule
    PRIVATE "src/granule.c"
            "src/tr_granule.c"
            "src/tracking_region.c"
            "src/tracking_region_sro.c"
            "src/tracking_region_transition.c")

if(RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-lib-granule
        PRIVATE "src/fake_host/tracking_region_arch.c")
endif()

include (tests/CMakeLists.txt)

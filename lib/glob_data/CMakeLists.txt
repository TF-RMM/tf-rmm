#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-glob_data)

target_link_libraries(rmm-lib-glob_data
    PUBLIC rmm-lib-xlat
           rmm-lib-common
    PRIVATE rmm-lib-debug
            rmm-lib-granule
            rmm-lib-xlat_low_va
            rmm-lib-rmm_el3_ifc
            rmm-lib-smmuv3)

target_include_directories(rmm-lib-glob_data
    PUBLIC "include"
    PRIVATE "src"
            "src/${RMM_ARCH}")

if(HOST_VARIANT STREQUAL "host_cbmc")
    target_sources(rmm-lib-glob_data
        PRIVATE "src/fake_host/cbmc_glob_data.c")
    return()
endif()

target_sources(rmm-lib-glob_data
            PRIVATE "src/glob_data.c")

#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-rmm_el3_ifc)

target_include_directories(rmm-lib-rmm_el3_ifc
    PUBLIC "include"
    PRIVATE "src")

target_link_libraries(rmm-lib-rmm_el3_ifc
    PRIVATE
        rmm-lib-arch
        rmm-lib-common
        rmm-lib-debug
        rmm-lib-xlat
        rmm-lib-smc)

target_sources(rmm-lib-rmm_el3_ifc
    PRIVATE "src/rmm_el3_ifc.c"
            "src/rmm_el3_ifc_manifest.c"
            "src/rmm_el3_runtime.c")

if (NOT RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-lib-rmm_el3_ifc
        PRIVATE "src/${RMM_ARCH}/rmm_el3_ifc_helpers.S")
endif()

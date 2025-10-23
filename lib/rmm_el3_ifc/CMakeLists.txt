#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-rmm_el3_ifc)

if (RMM_EL3_COMPAT_RESERVE_MEM)
    target_compile_definitions(rmm-lib-rmm_el3_ifc
        PUBLIC "RMM_EL3_COMPAT_RESERVE_MEM=1")
endif()

target_include_directories(rmm-lib-rmm_el3_ifc
    PUBLIC "include"
    PRIVATE "src")

target_link_libraries(rmm-lib-rmm_el3_ifc
    PRIVATE
        rmm-lib-arch
        rmm-lib-common
        rmm-lib-debug
    PUBLIC
        rmm-lib-smc)

if(RMM_ARCH STREQUAL fake_host)
    target_link_libraries(rmm-lib-rmm_el3_ifc
        PRIVATE
            rmm-host-el2-el0-cmn)
endif()

if(HOST_VARIANT STREQUAL "host_cbmc")
    target_sources(rmm-lib-rmm_el3_ifc
        PRIVATE "src/fake_host/cbmc_rmm_el3_ifc.c"
                "src/fake_host/cbmc_rmm_el3_ifc_manifest.c"
                "src/fake_host/cbmc_rmm_el3_rp_ide_km.c")
    # In case of 'host_cbmc' variant no further source files are added to
    # the build.
    return()
endif()

target_sources(rmm-lib-rmm_el3_ifc
    PRIVATE "src/rmm_el3_ifc.c"
            "src/rmm_el3_ifc_manifest.c"
            "src/rmm_el3_runtime.c"
            "src/rmm_el3_rp_ide_km.c"
            "src/rmm_el3_compat.c")

if (NOT RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-lib-rmm_el3_ifc
        PRIVATE "src/${RMM_ARCH}/rmm_el3_ifc_helpers.S")
endif()

#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-plat-host_build)

target_link_libraries(rmm-plat-host_build
    PRIVATE rmm-host-harness
            rmm-lib
            rmm-el2-stub)

target_include_directories(rmm-plat-host_build
    PRIVATE "src")

target_sources(rmm-plat-host_build
    PRIVATE "src/host_setup.c"
            "src/host_harness.c"
            "src/host_realm_attest_rsi.c"
            "src/host_da.c"
            "src/host_spdm_rsp_ifc.c"
            "src/host_da_crypto_utils.c"
            "src/host_realm_da_rsi.c")

add_library(rmm-platform ALIAS rmm-plat-host_build)

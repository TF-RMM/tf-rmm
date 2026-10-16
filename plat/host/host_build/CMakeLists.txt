#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-plat-host_build)

target_link_libraries(rmm-plat-host_build
    PRIVATE rmm-host-da
            rmm-host-harness
            rmm-lib)

target_include_directories(rmm-plat-host_build
    PRIVATE "${CMAKE_SOURCE_DIR}/ext/minicoro"
            "src")

target_sources(rmm-plat-host_build
    PRIVATE "src/host_setup.c"
            "src/host_harness.c"
            "src/host_realm_attest_rsi.c"
            "src/host_realm_da_rsi.c")

add_library(rmm-platform ALIAS rmm-plat-host_build)

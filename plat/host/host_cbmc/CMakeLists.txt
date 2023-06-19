#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-plat-host_cbmc)

target_link_libraries(rmm-plat-host_cbmc
    PRIVATE rmm-lib
    PUBLIC rmm-host-common)

target_sources(rmm-plat-host_cbmc
    PRIVATE "src/host_harness.c")

target_include_directories(rmm-plat-host_cbmc
    PUBLIC "include")

add_library(rmm-platform ALIAS rmm-plat-host_cbmc)

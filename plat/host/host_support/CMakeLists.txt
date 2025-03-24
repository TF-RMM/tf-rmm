#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-host-support)

target_link_libraries(rmm-host-support
    PRIVATE
        rmm-common
        rmm-lib-arch
        rmm-lib-common)

target_sources(rmm-host-support
    PRIVATE "src/host_spinlock.c"
            "src/host_sysregs.c")

target_include_directories(rmm-host-support
    PUBLIC "include"
    PRIVATE "src")

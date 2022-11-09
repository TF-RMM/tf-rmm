#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-asc)

target_link_libraries(rmm-lib-asc
    PRIVATE rmm-lib-common
            rmm-lib-smc)

target_include_directories(rmm-lib-asc
    PUBLIC "include")

target_sources(rmm-lib-asc
    PRIVATE "src/asc_drv.c")

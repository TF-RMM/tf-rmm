#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-gic)

target_link_libraries(rmm-lib-gic
    PRIVATE rmm-lib-arch
            rmm-lib-common
            rmm-lib-debug
            rmm-lib-smc)

target_include_directories(rmm-lib-gic
    PUBLIC "include")

target_sources(rmm-lib-gic
    PRIVATE "src/gic.c")

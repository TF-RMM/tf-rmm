#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-sro_context)

target_link_libraries(rmm-lib-sro_context
    PRIVATE rmm-lib-arch
            rmm-lib-debug
            rmm-lib-smc)

target_include_directories(rmm-lib-sro_context
    PUBLIC "include")

target_sources(rmm-lib-sro_context
    PRIVATE "src/sro_context.c")

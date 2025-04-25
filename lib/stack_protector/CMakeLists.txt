#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-stack_protector)

target_include_directories(rmm-lib-stack_protector
    PUBLIC "include"
    PRIVATE "src")

target_link_libraries(rmm-lib-stack_protector
    PRIVATE rmm-lib-common
            rmm-lib-debug
            rmm-lib-arch)


target_sources(rmm-lib-stack_protector PRIVATE "src/stack_protector.c")

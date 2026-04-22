#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-addr_list)

target_link_libraries(rmm-lib-addr_list
    PRIVATE rmm-lib-arch
            rmm-lib-debug
            rmm-lib-slot_buf
    PUBLIC  rmm-lib-granule
            rmm-lib-xlat)

target_include_directories(rmm-lib-addr_list
    PUBLIC "include"
    PRIVATE "src")

target_sources(rmm-lib-addr_list
    PRIVATE "src/addr_list.c")

include(tests/CMakeLists.txt)

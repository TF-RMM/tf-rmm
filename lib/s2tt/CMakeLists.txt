#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-s2tt)

target_link_libraries(rmm-lib-s2tt
    PRIVATE rmm-lib-arch
            rmm-lib-common
            rmm-lib-debug
            rmm-lib-slot_buf
            rmm-lib-smc
    PUBLIC  rmm-lib-granule)

target_include_directories(rmm-lib-s2tt
    PUBLIC "include"
    PRIVATE "src")

target_sources(rmm-lib-s2tt
    PRIVATE "src/s2tt.c")

include (tests/CMakeLists.txt)

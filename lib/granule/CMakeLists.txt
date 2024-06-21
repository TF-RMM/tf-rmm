#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-granule)

target_link_libraries(rmm-lib-granule
    PUBLIC rmm-lib-arch
           rmm-lib-common
    PRIVATE rmm-lib-debug)

target_include_directories(rmm-lib-granule
    PUBLIC "include"
           "include/${RMM_ARCH}")

target_sources(rmm-lib-granule
    PRIVATE "src/granule.c")

include (tests/CMakeLists.txt)

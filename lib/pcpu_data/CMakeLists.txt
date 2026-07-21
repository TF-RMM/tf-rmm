#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-pcpu_data)

target_include_directories(rmm-lib-pcpu_data
    PUBLIC "include"
           "include/${RMM_ARCH}"
    PRIVATE "src")

target_link_libraries(rmm-lib-pcpu_data
    PRIVATE
        rmm-lib-common
        rmm-lib-debug
    PUBLIC
        rmm-lib-arch
        rmm-lib-xlat)

if (NOT RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-lib-pcpu_data
        PRIVATE "src/${RMM_ARCH}/pcpu_data_helpers.S")
else()
    target_sources(rmm-lib-pcpu_data
        PRIVATE "src/fake_host/pcpu_data_setup.c")
endif()

target_sources(rmm-lib-pcpu_data
    PRIVATE "src/pcpu_data.c")

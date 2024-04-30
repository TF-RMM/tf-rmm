#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-slot_buf)

target_link_libraries(rmm-lib-slot_buf
    PRIVATE rmm-lib-arch
            rmm-lib-common
            rmm-lib-debug
            rmm-lib-xlat)

target_link_libraries(rmm-lib-slot_buf
    PUBLIC rmm-lib-granule
           rmm-lib-smc)

target_include_directories(rmm-lib-slot_buf
    PUBLIC "include"
    PRIVATE "src/include"
            "src/include/${RMM_ARCH}")

if(RMM_ARCH STREQUAL fake_host)
    # Needed to access the platform callbacks.
    target_link_libraries(rmm-lib-slot_buf
        PRIVATE rmm-platform)
else()
    target_sources(rmm-lib-slot_buf
        PRIVATE "src/aarch64/ns_access.S")
endif()

target_sources(rmm-lib-slot_buf
    PRIVATE "src/buffer.c")

include (tests/CMakeLists.txt)


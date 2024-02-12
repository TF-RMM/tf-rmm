#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-slot_buf)

arm_config_option(
    NAME VIRT_ADDR_SPACE_WIDTH
    HELP "Size in bits of the virtual address space."
    DEFAULT 38
    TYPE STRING
    ADVANCED)

if(VIRT_ADDR_SPACE_WIDTH EQUAL 0x0)
    message(FATAL_ERROR "VIRT_ADDR_SPACE_WIDTH is not initialized")
endif()

target_compile_definitions(rmm-lib-slot_buf
    PUBLIC "VIRT_ADDR_SPACE_SIZE=(1ULL << ULL(${VIRT_ADDR_SPACE_WIDTH}))")

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


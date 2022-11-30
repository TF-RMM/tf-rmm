#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-realm)

arm_config_option(
    NAME VIRT_ADDR_SPACE_WIDTH
    HELP "Size in bits of the virtual address space."
    DEFAULT 0x0
    TYPE STRING
    ADVANCED)

#
# RMM_MAX_GRANULES. Maximum number of granules supported.
#
arm_config_option(
    NAME RMM_MAX_GRANULES
    HELP "Maximum number of granules supported"
    DEFAULT 0x0
    TYPE STRING)

if(VIRT_ADDR_SPACE_WIDTH EQUAL 0x0)
    message(FATAL_ERROR "VIRT_ADDR_SPACE_WIDTH is not initialized")
endif()

target_compile_definitions(rmm-lib-realm
    PUBLIC "VIRT_ADDR_SPACE_SIZE=(1ULL << ULL(${VIRT_ADDR_SPACE_WIDTH}))")

if (RMM_MAX_GRANULES EQUAL 0x0)
    message (FATAL_ERROR "RMM_MAX_GRANULES not configured")
endif()

# Export RMM_MAX_GRANULES for use in `plat` component.
target_compile_definitions(rmm-lib-realm
    PUBLIC "RMM_MAX_GRANULES=U(${RMM_MAX_GRANULES})")

target_link_libraries(rmm-lib-realm
    PRIVATE rmm-lib-arch
            rmm-lib-common
            rmm-lib-debug
            rmm-lib-gic
            rmm-lib-xlat
            rmm-lib-allocator
            rmm-lib-attestation
            rmm-platform)

target_link_libraries(rmm-lib-realm
    PUBLIC rmm-lib-measurement
           rmm-lib-smc)

target_include_directories(rmm-lib-realm
    PUBLIC "include"
    PRIVATE "src/include/${RMM_ARCH}"
    PRIVATE "src/include")

target_sources(rmm-lib-realm
    PRIVATE "src/buffer.c"
            "src/granule.c"
            "src/s2tt.c"
            "src/sve.c")

if(NOT RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-lib-realm
        PRIVATE "src/aarch64/sve_helpers.S")
endif()

include (tests/CMakeLists.txt)

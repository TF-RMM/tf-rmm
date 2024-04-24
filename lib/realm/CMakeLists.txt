#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-realm)

arm_config_option(
    NAME VIRT_ADDR_SPACE_WIDTH
    HELP "Size in bits of the virtual address space."
    DEFAULT 38
    TYPE STRING
    ADVANCED)

if(VIRT_ADDR_SPACE_WIDTH EQUAL 0x0)
    message(FATAL_ERROR "VIRT_ADDR_SPACE_WIDTH is not initialized")
endif()

target_compile_definitions(rmm-lib-realm
    PUBLIC "VIRT_ADDR_SPACE_SIZE=(1ULL << ULL(${VIRT_ADDR_SPACE_WIDTH}))")

target_link_libraries(rmm-lib-realm
    PRIVATE rmm-lib-arch
            rmm-lib-common
            rmm-lib-debug
            rmm-lib-xlat)

# Needed to link with the platform callbacks for buffer map/unmap
if(RMM_ARCH STREQUAL fake_host)
    target_link_libraries(rmm-lib-realm
        PRIVATE rmm-platform)
endif()

target_link_libraries(rmm-lib-realm
    PUBLIC rmm-lib-attestation
           rmm-lib-gic
           rmm-lib-measurement
           rmm-lib-s2tt
           rmm-lib-smc)

target_include_directories(rmm-lib-realm
    PUBLIC "include"
    PRIVATE "src/include/${RMM_ARCH}"
    PRIVATE "src/include")

target_sources(rmm-lib-realm
    PRIVATE "src/buffer.c"
            "src/granule.c")

include (tests/CMakeLists.txt)

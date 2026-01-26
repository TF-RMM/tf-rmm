#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# This cmake file is meant to be included from plat CMakelists.txt
#
add_library(rmm-plat-common)

target_link_libraries(rmm-plat-common
    PRIVATE rmm-lib
            rmm-el2-stub)

#
# Default Stage 1 virtual address space width for a given platform.
#
arm_config_option(
    NAME PLAT_CMN_VIRT_ADDR_SPACE_WIDTH
    HELP "Size in bits of the virtual address space."
    DEFAULT 38
    TYPE STRING
    ADVANCED)

if(PLAT_CMN_VIRT_ADDR_SPACE_WIDTH EQUAL 0x0)
    message(FATAL_ERROR "PLAT_CMN_VIRT_ADDR_SPACE_WIDTH is not initialized")
endif()

target_compile_definitions(rmm-plat-common
    PRIVATE "PLAT_CMN_VIRT_ADDR_SPACE_SIZE=(1ULL << ULL(${PLAT_CMN_VIRT_ADDR_SPACE_WIDTH}))")

target_include_directories(rmm-plat-common
    PUBLIC "include"
    PRIVATE "src/${RMM_ARCH}")

target_sources(rmm-plat-common
    PRIVATE "src/plat_common_init.c"
            "src/plat_compat_mem.c")

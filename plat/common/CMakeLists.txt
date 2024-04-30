#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# This cmake file is meant to be included from plat CMakelists.txt
#
add_library(rmm-plat-common)

target_link_libraries(rmm-plat-common
    PRIVATE rmm-lib)

#
# PLAT_CMN_CTX_MAX_XLAT_TABLES is allowed to be 0, and in case when there are
# not enough tables the xlat tables creation will fail.
#
arm_config_option(
    NAME PLAT_CMN_CTX_MAX_XLAT_TABLES
    HELP "Maximum number of translation tables to be allocated for the static xlat tables"
    DEFAULT 0x0
    TYPE STRING)

#
# Number of extra mmap regions to be allocated for a given platform.
# This is allowed to be 0. If the number of platform memory regions
# needed by a given platform is lower than PLAT_CMN_EXTRA_MMAP_REGIONS,
# the xlat library should fail when trying to initialize the context.
#
arm_config_option(
    NAME PLAT_CMN_EXTRA_MMAP_REGIONS
    HELP "Extra platform mmap regions that need to be mapped in S1 xlat tables"
    DEFAULT 0
    TYPE STRING)

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
    PRIVATE "PLAT_CMN_CTX_MAX_XLAT_TABLES=U(${PLAT_CMN_CTX_MAX_XLAT_TABLES})")

target_compile_definitions(rmm-plat-common
    PRIVATE "PLAT_CMN_EXTRA_MMAP_REGIONS=U(${PLAT_CMN_EXTRA_MMAP_REGIONS})")

target_compile_definitions(rmm-plat-common
    PRIVATE "PLAT_CMN_VIRT_ADDR_SPACE_SIZE=(1ULL << ULL(${PLAT_CMN_VIRT_ADDR_SPACE_WIDTH}))")

target_include_directories(rmm-plat-common
    PUBLIC "include"
    PRIVATE "src/${RMM_ARCH}")

target_sources(rmm-plat-common
    PRIVATE "src/plat_common_init.c")

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
# PLAT_CMN_MAX_MMAP_REGIONS is set a default value and in case when there are
# not enough mmap regions allocated, adding regions to the xlat tables will
# fail.
#
arm_config_option(
    NAME PLAT_CMN_MAX_MMAP_REGIONS
    HELP "Maximum number of static regions to be mapped in xlat tables"
    DEFAULT 0x5
    TYPE STRING)

target_compile_definitions(rmm-plat-common
    PUBLIC "PLAT_CMN_CTX_MAX_XLAT_TABLES=U(${PLAT_CMN_CTX_MAX_XLAT_TABLES})")

target_compile_definitions(rmm-plat-common
    PUBLIC "PLAT_CMN_MAX_MMAP_REGIONS=U(${PLAT_CMN_MAX_MMAP_REGIONS})")

target_include_directories(rmm-plat-common
    PUBLIC "include")

target_sources(rmm-plat-common
    PRIVATE "src/plat_common_init.c")

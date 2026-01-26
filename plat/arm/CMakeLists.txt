#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Additional config for maximum possible number of DRAM and COH/NCOH device memory banks allowed to be managed
#
arm_config_option(
    NAME PLAT_ARM_MAX_MEM_BANKS
    HELP "Maximum possible number of DRAM and COH/NCOH device memory banks allowed in Arm platform layer"
    TYPE STRING
    DEFAULT 0x2)

add_library(rmm-plat-arm)

#
# RMM_EL3_COMPAT_RESERVE_MEM. Reserved memory for RMM compatibility.
# This is used when EL3 does not support RMM_RESERVE_MEMORY SMC.
# Enabled by default. This option is passed to compiler definitions
# by rmm-el3-ifc library.
#
arm_config_option(
    NAME RMM_EL3_COMPAT_RESERVE_MEM
    HELP "Reserved memory for RMM compatibility"
    TYPE BOOL
    DEFAULT TRUE)

# Warn that COMPAT_RESERVE_MEM is enabled and LFA is not supported.
if(RMM_EL3_COMPAT_RESERVE_MEM)
    message(WARNING "RMM_EL3_COMPAT_RESERVE_MEM is enabled. LFA is not supported.")
endif()

# RMM_MAX_GRANULES. Maximum number of memory granules supported.
arm_config_option(
    NAME RMM_MAX_GRANULES
    HELP "Maximum number of memory granules supported"
    TYPE STRING
    DEFAULT 0x0
    DEPENDS RMM_EL3_COMPAT_RESERVE_MEM)

# RMM_MAX_COH_GRANULES. Maximum number of coherent device granules supported.
arm_config_option(
    NAME RMM_MAX_COH_GRANULES
    HELP "Maximum number of coherent device granules supported"
    TYPE STRING
    DEFAULT 1
    DEPENDS RMM_EL3_COMPAT_RESERVE_MEM
    ELSE 0x0)

# RMM_MAX_NCOH_GRANULES. Maximum number of non-coherent device granules supported.
arm_config_option(
    NAME RMM_MAX_NCOH_GRANULES
    HELP "Maximum number of non-coherent device granules supported"
    TYPE STRING
    DEFAULT 1
    DEPENDS RMM_EL3_COMPAT_RESERVE_MEM
    ELSE 0x0)

# PLAT_CMN_CTX_MAX_XLAT_TABLES is allowed to be 0, and in case when there are
# not enough tables the xlat tables creation will fail.
arm_config_option(
    NAME PLAT_CMN_CTX_MAX_XLAT_TABLES
    HELP "Maximum number of translation tables to be allocated for the static xlat tables"
    DEFAULT 0x0
    TYPE STRING
    DEPENDS RMM_EL3_COMPAT_RESERVE_MEM)

if (NOT RMM_MAX_GRANULES EQUAL 0x0)
    target_compile_definitions(rmm-plat-arm
        PRIVATE "RMM_MAX_GRANULES=U(${RMM_MAX_GRANULES})")
endif()

if (NOT RMM_MAX_COH_GRANULES EQUAL 0x0)
    target_compile_definitions(rmm-plat-arm
        PRIVATE "RMM_MAX_COH_GRANULES=U(${RMM_MAX_COH_GRANULES})")
endif()

if (NOT RMM_MAX_NCOH_GRANULES EQUAL 0x0)
    target_compile_definitions(rmm-plat-arm
        PRIVATE "RMM_MAX_NCOH_GRANULES=U(${RMM_MAX_NCOH_GRANULES})")
endif()

if (NOT PLAT_CMN_CTX_MAX_XLAT_TABLES EQUAL 0x0)
    target_compile_definitions(rmm-plat-arm
        PRIVATE "PLAT_CMN_CTX_MAX_XLAT_TABLES=U(${PLAT_CMN_CTX_MAX_XLAT_TABLES})")
endif()

add_subdirectory("${RMM_SOURCE_DIR}/drivers/pl011" ${RMM_BINARY_DIR}/drivers/pl011)
add_subdirectory("${RMM_SOURCE_DIR}/plat/common" ${RMM_BINARY_DIR}/plat/common)

if(PLAT_ARM_MAX_MEM_BANKS EQUAL 0x0)
    message(FATAL_ERROR "Invalid PLAT_ARM_MAX_MEM_BANKS")
endif()

target_compile_definitions(rmm-plat-arm
    PRIVATE "PLAT_ARM_MAX_MEM_BANKS=U(${PLAT_ARM_MAX_MEM_BANKS})")

target_link_libraries(rmm-plat-arm
    PRIVATE rmm-driver-pl011
            rmm-lib
            rmm-plat-common)

target_sources(rmm-plat-arm
    PRIVATE "src/arm_setup.c"
            "src/arm_granule.c"
            "src/arm_memory.c"
            "src/arm_root_complex.c")

target_include_directories(rmm-plat-arm
    PRIVATE "src/include")

add_library(rmm-platform ALIAS rmm-plat-arm)

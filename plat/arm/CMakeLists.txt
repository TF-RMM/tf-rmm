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
# Extra memory regions needed by this platform
#
arm_config_option_override(NAME PLAT_CMN_EXTRA_MMAP_REGIONS DEFAULT 1)

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

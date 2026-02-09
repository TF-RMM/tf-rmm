#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-xlat_low_va)

#
# Configuration option to set the size of the RMM VA pool.
# DEFAULT is set to 1GB.
#
arm_config_option(
    NAME RMM_VA_POOL_SIZE
    HELP "Size of the RMM virtual address pool for dynamic allocations"
    TYPE STRING
    DEFAULT "0x40000000"
)
# Check that RMM_VA_POOL_SIZE is a multiple of 1GB.
math(EXPR RMM_VA_POOL_SIZE_MOD "(${RMM_VA_POOL_SIZE} % 0x40000000)")
if(NOT RMM_VA_POOL_SIZE_MOD EQUAL 0)
    message(FATAL_ERROR "RMM_VA_POOL_SIZE (${RMM_VA_POOL_SIZE}) must be a multiple of 1GB (0x40000000)")
endif()

# Check that RMM_VA_POOL_SIZE is less than 512GB
math(EXPR RMM_VA_POOL_SIZE_MAX "0x8000000000")
if(NOT RMM_VA_POOL_SIZE LESS RMM_VA_POOL_SIZE_MAX)
    message(FATAL_ERROR "RMM_VA_POOL_SIZE (${RMM_VA_POOL_SIZE}) must be less than 512GB (0x8000000000)")
endif()

target_compile_definitions(rmm-lib-xlat_low_va
        PUBLIC "RMM_VA_POOL_SIZE=UL(${RMM_VA_POOL_SIZE})")

target_link_libraries(rmm-lib-xlat_low_va
    PRIVATE rmm-lib-arch
            rmm-lib-common
            rmm-lib-debug
            rmm-lib-rmm_el3_ifc
            rmm-lib-xlat)

target_include_directories(rmm-lib-xlat_low_va
    PUBLIC "include"
    PRIVATE "src"
        "src/${RMM_ARCH}")

if(HOST_VARIANT STREQUAL "host_cbmc")
    target_sources(rmm-lib-xlat_low_va
        PRIVATE "src/fake_host/cbmc_xlat_low_va.c")
    # In case of 'host_cbmc' variant no further source files are added to
    # the build.
    return()
endif()

target_sources(rmm-lib-xlat_low_va
    PRIVATE "src/xlat_low_va.c")

include(tests/CMakeLists.txt)

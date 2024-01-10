#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-xlat)

target_link_libraries(rmm-lib-xlat
    PRIVATE rmm-lib-common
            rmm-lib-libc
            rmm-lib-arch
            rmm-lib-debug)

target_include_directories(rmm-lib-xlat
    PUBLIC "include")

target_include_directories(rmm-lib-xlat
    PRIVATE "src")

arm_config_option(
    NAME XLAT_GRANULARITY_SIZE_SHIFT
    HELP "Size in bits of the translation granularity"
    TYPE STRING
    STRINGS "12" "14" "16"
    DEFAULT "12"
    ADVANCED)

if(NOT(XLAT_GRANULARITY_SIZE_SHIFT EQUAL "12"))
    message(FATAL_ERROR "Only 4K granularity is supported at the moment")
endif()

target_compile_definitions(rmm-lib-xlat
    PUBLIC "XLAT_GRANULARITY_SIZE_SHIFT=UL(${XLAT_GRANULARITY_SIZE_SHIFT})")

include (tests/CMakeLists.txt)

if(RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-lib-xlat
        PRIVATE "src/fake_host/enable_mmu.c"
                "src/fake_host/xlat_helpers.c")
else()
    target_sources(rmm-lib-xlat
        PRIVATE "src/aarch64/enable_mmu.S"
                "src/aarch64/xlat_helper.S")
endif()

if(HOST_VARIANT STREQUAL "host_cbmc")
    target_sources(rmm-lib-xlat
        PRIVATE "src/fake_host/cbmc_xlat_tables_utils.c"
                "src/fake_host/cbmc_xlat_high_va.c")
    # In case of 'host_cbmc' variant no further source files are added to
    # the build.
    return()
endif()

target_sources(rmm-lib-xlat
    PRIVATE "src/xlat_tables_core.c"
            "src/xlat_tables_utils.c"
            "src/xlat_tables_arch.c"
            "src/xlat_contexts.c"
            "src/xlat_high_va.c")

#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Common config options
#
arm_config_option(
    NAME MAX_CPUS
    HELP "Maximum number of CPUs supported by RMM"
    TYPE STRING
    DEFAULT 16)

#
# The RMM is mapped with 4K pages, and all RMM APIs use the same granularity.
#
arm_config_option(
    NAME GRANULE_SIZE
    HELP "Granule Size used by RMM"
    TYPE STRING
    DEFAULT 4096)

#
# RMM_MAX_GRANULES. Maximum number of granules supported.
#
arm_config_option(
    NAME RMM_MAX_GRANULES
    HELP "Maximum number of granules supported"
    TYPE STRING
    DEFAULT 0x0)

arm_config_option(
    NAME RMM_DOCS
    HELP "RMM Documentation build"
    TYPE BOOL
    DEFAULT OFF)

# TODO: Move to lib/arch once MbedTLS compilation is moved to build phase.
arm_config_option(
    NAME RMM_FPU_USE_AT_REL2
    HELP "Enable Advanced SIMD support in RMM"
    TYPE BOOL
    DEFAULT ON
    DEPENDS (RMM_ARCH STREQUAL aarch64)
    ELSE OFF)

#
# Introduce a pseudo-library purely for applying flags to RMM's libraries.
# This is applied to any targets created after this point.
#

add_library(rmm-common INTERFACE)

target_compile_definitions(rmm-common
    INTERFACE "$<$<CONFIG:Debug>:DEBUG>")

if(MAX_CPUS EQUAL 0x0)
    message(FATAL_ERROR "MAX_CPUS is not initialized")
endif()

target_compile_definitions(rmm-common
    INTERFACE "MAX_CPUS=${MAX_CPUS}U")

if(NOT(GRANULE_SIZE EQUAL 4096))
    message(FATAL_ERROR "GRANULE_SIZE is not initialized correctly")
endif()

target_compile_definitions(rmm-common
    INTERFACE "GRANULE_SIZE=UL(${GRANULE_SIZE})")

if (RMM_MAX_GRANULES EQUAL 0x0)
    message (FATAL_ERROR "RMM_MAX_GRANULES not configured")
endif()

target_compile_definitions(rmm-common
    INTERFACE "RMM_MAX_GRANULES=U(${RMM_MAX_GRANULES})")

if(RMM_FPU_USE_AT_REL2)
    target_compile_definitions(rmm-common
        INTERFACE "RMM_FPU_USE_AT_REL2=1")
endif()

#
# Project name and version
#
target_compile_definitions(rmm-common
    INTERFACE "NAME=\"${PROJECT_NAME}\"")

target_compile_definitions(rmm-common
    INTERFACE "VERSION=\"${PROJECT_VERSION}\"")

#
# Get git commit information
#
find_package(Git)
if(GIT_FOUND)
  execute_process(
    COMMAND ${GIT_EXECUTABLE} describe --always --dirty --tags
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    OUTPUT_VARIABLE COMMIT_INFO
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
endif()

target_compile_definitions(rmm-common
    INTERFACE "COMMIT_INFO=\"${COMMIT_INFO}\"")

link_libraries(rmm-common)

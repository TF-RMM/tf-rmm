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
    NAME GRANULE_SHIFT
    HELP "The shift value of granule size. i.e: GRANULE_SIZE == 1 << GRANULE_SHIFT"
    TYPE STRING
    DEFAULT 12)

#
# RMM_MAX_GRANULES. Maximum number of granules supported.
#
arm_config_option(
    NAME RMM_MAX_GRANULES
    HELP "Maximum number of granules supported"
    TYPE STRING
    DEFAULT 0x0)

arm_config_option(
    NAME RMM_NUM_PAGES_PER_STACK
    HELP "Number of pages to use per CPU stack"
    TYPE STRING
    DEFAULT 5
    ADVANCED)

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
    DEFAULT OFF)

#
# The number of 4K pages allocated for attestation buffer.
#
arm_config_option(
    NAME RMM_CCA_TOKEN_BUFFER
    HELP "Number of pages to allocate in Aux granules for Realm CCA token"
    TYPE STRING
    DEFAULT 1)

arm_config_option(
    NAME RMM_V1_1
    HELP "Enable v1.1 features in RMM (experimental)"
    TYPE BOOL
    DEFAULT OFF)

arm_config_option(
    NAME ATTEST_EL3_TOKEN_SIGN
    HELP "Use EL3 service to sign realm attestation token."
    TYPE BOOL
    DEFAULT OFF
    ADVANCED)

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

if(NOT(GRANULE_SHIFT EQUAL 12))
    message(FATAL_ERROR "GRANULE_SHIFT is not initialized correctly")
endif()

target_compile_definitions(rmm-common
    INTERFACE "GRANULE_SHIFT=U(${GRANULE_SHIFT})")

if (RMM_MAX_GRANULES EQUAL 0x0)
    message (FATAL_ERROR "RMM_MAX_GRANULES not configured")
endif()

target_compile_definitions(rmm-common
    INTERFACE "RMM_MAX_GRANULES=U(${RMM_MAX_GRANULES})")

target_compile_definitions(rmm-common
    INTERFACE "RMM_NUM_PAGES_PER_STACK=UL(${RMM_NUM_PAGES_PER_STACK})")

if(RMM_FPU_USE_AT_REL2 AND RMM_ARCH STREQUAL aarch64)
    target_compile_definitions(rmm-common
        INTERFACE "RMM_FPU_USE_AT_REL2=1")
endif()

target_compile_definitions(rmm-common
    INTERFACE "RMM_CCA_TOKEN_BUFFER=U(${RMM_CCA_TOKEN_BUFFER})")

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

if(RMM_V1_1)
    message(WARNING "RMM v1.1 features are experimental")
    target_compile_definitions(rmm-common
        INTERFACE "RMM_V1_1=1")
endif()

link_libraries(rmm-common)

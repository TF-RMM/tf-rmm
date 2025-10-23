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
# RMM_MAX_SMMUS. Maximum number of SMMUv3 supported.
#
arm_config_option(
    NAME RMM_MAX_SMMUS
    HELP "Maximum number of SMMUv3 supported"
    TYPE STRING
    DEFAULT 0x1)

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
# Enable the Stack protection compiler flag.
# Having the PAUTH and BTI feature enabled makes the software-based
# stack frame canary redundant. Enabling the software canary could
# have a performance degradation. Hence the default is OFF.
#
arm_config_option(
	NAME STACK_PROTECTOR
	HELP "Enable Stack Protection Compiler Flags"
	string OFF)

#
# Method to scrub the memory before returning the granule back to NS.
# Valid values are 0, 1 and 2. The details of each method can be found
# in MEC design document.
#
arm_config_option(
    NAME RMM_MEM_SCRUB_METHOD
    HELP "Method to Sanitize memory. Valid values are 0 (default), 1 & 2."
    TYPE STRINGS "0" "1" "2")

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

if(RMM_MAX_SMMUS EQUAL 0x0)
    message(FATAL_ERROR "RMM_MAX_SMMUS  cannot be set to 0")
endif()

target_compile_definitions(rmm-common
    INTERFACE "RMM_MAX_SMMUS=U(${RMM_MAX_SMMUS})")

target_compile_definitions(rmm-common
    INTERFACE "RMM_NUM_PAGES_PER_STACK=UL(${RMM_NUM_PAGES_PER_STACK})")

# Set stack protector option.
if(STACK_PROTECTOR)
	target_compile_definitions(rmm-common
	INTERFACE "STACK_PROTECTOR_ENABLED=1")
	message(STATUS "Stack Protector is Enabled.")
	add_compile_options(-fstack-protector-strong)
endif()

if (RMM_MEM_SCRUB_METHOD STREQUAL "0")
    message(STATUS "Default RMM_MEM_SCRUB_METHOD selected.")
elseif (RMM_MEM_SCRUB_METHOD STREQUAL "1")
    message(STATUS "RMM_MEM_SCRUB_METHOD 1 selected.")
    target_compile_definitions(rmm-common
        INTERFACE "RMM_MEM_SCRUB_METHOD=1")
elseif (RMM_MEM_SCRUB_METHOD STREQUAL "2")
    message(STATUS "RMM_MEM_SCRUB_METHOD 2 selected.")
    target_compile_definitions(rmm-common
        INTERFACE "RMM_MEM_SCRUB_METHOD=2")
else()
    message (FATAL_ERROR "Invalid RMM_MEM_SCRUB_METHOD selected.")
endif()

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
Git_Get_Commit_Info(COMMIT_INFO)

target_compile_definitions(rmm-common
    INTERFACE "COMMIT_INFO=\"${COMMIT_INFO}\"")

if(RMM_V1_1)
    message(WARNING "RMM v1.1 features are experimental")
    target_compile_definitions(rmm-common
        INTERFACE "RMM_V1_1=1")
endif()

link_libraries(rmm-common)

#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

cmake_minimum_required(VERSION 3.15.0)

# allow target_link_libraries() to be used with targets in other directories
cmake_policy(SET CMP0079 NEW)

#
# Add our module search paths so we can `include()` our CMake modules.
#

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_LIST_DIR}/cmake/Modules")

#
# Include any dependencies.
#

include(ArmConfigOption)
include(ArmConfigOptionOverride)

#
# Run preliminary setup scripts.
#
set(RMM_CONFIG_FILE "${CMAKE_SOURCE_DIR}/configs/${RMM_CONFIG}.cmake")
if(NOT EXISTS ${RMM_CONFIG_FILE})
    message(FATAL_ERROR "Please provide config ${RMM_CONFIG_FILE}")
endif()

include("${RMM_CONFIG_FILE}")

#
# Set the target build Architecture before we proceed further.
# Default is aarch64.
#
arm_config_option(
        NAME RMM_ARCH
        HELP "Target Architecture for RMM build."
        STRINGS "aarch64" "fake_host")

include("cmake/Toolchains.cmake")
include("cmake/BuildType.cmake")

#
# Initialize the project. Note that this is where the toolchain file is loaded,
# and also where the project directory and version variables are set up.
#

project(RMM VERSION 0.2.0 LANGUAGES ASM C)

#
# Set global flags.
#

set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED TRUE)
set(CMAKE_C_EXTENSIONS TRUE)

if(RMM_STATIC_ANALYSIS_CPPCHECK)
    set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
endif()
#
# Include the platform makefile
#
include("cmake/Platforms.cmake")

#
# Include the common configuration options
#
include("cmake/CommonConfigs.cmake")

#
# Load in our C standard library and link it to any targets created after this
# point. This will automatically transition these targets away from the standard
# library provided by the toolchain, and towards our libc.
#

add_subdirectory("lib/libc")

link_libraries(rmm-lib-libc)

#
# Build the MbedTLS we package in the source tree, and import the targets from
# it so that we can model the library dependency properly.
#

include("cmake/BuildMbedTLS.cmake")

set(MbedTLS_ROOT "${MbedTLS_INSTALL_DIR}")
find_package(MbedTLS COMPONENTS Crypto REQUIRED)

target_link_libraries(MbedTLS
    INTERFACE rmm-lib-libc)

#
# Build and link QCBOR
#
include("cmake/BuildQCBOR.cmake")

#
# Recurse into the various component subdirectories
#
add_subdirectory("lib")
add_subdirectory("runtime")

if(RMM_DOCS)
    add_subdirectory("docs")
endif()

#
# Create the flat binary using whatever tool comes with the toolchain.
#

if(CMAKE_OBJCOPY)
    add_custom_command(
        COMMAND "${CMAKE_OBJCOPY}" -O binary "$<TARGET_FILE:rmm-runtime>" rmm.img
        OUTPUT rmm.img
        DEPENDS rmm-runtime)
endif()

#
# Create the dump file using whatever tool comes with the toolchain.
#

if(CMAKE_OBJDUMP)
    add_custom_command(
        COMMAND "${CMAKE_OBJDUMP}" -dx "$<TARGET_FILE:rmm-runtime>" > rmm.dump
        OUTPUT rmm.dump
        DEPENDS rmm-runtime)
endif()

#
# Copy 'rmm-runtime' executable to 'build\rmm.elf'.
#

add_custom_command(
    COMMAND "${CMAKE_COMMAND}" -E copy_if_different "$<TARGET_FILE:rmm-runtime>" rmm.elf
    OUTPUT rmm.elf
    DEPENDS rmm-runtime)

#
# Copy 'rmm-runtime.map' to 'build\rmm.map'
#

add_custom_command(
    COMMAND "${CMAKE_COMMAND}" -E copy_if_different "$<TARGET_FILE:rmm-runtime>.map" rmm.map
    OUTPUT rmm.map
    DEPENDS rmm-runtime)

add_custom_target(rmm ALL DEPENDS rmm.img rmm.dump rmm.elf rmm.map)

#
# Set up additional tooling.
#

add_subdirectory("tools")

#
# Rules for checkpatch
#

add_custom_target(checkcodebase
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND} -DCHECKCODEBASE_RUN=1 -P ${CMAKE_SOURCE_DIR}/tools/checkpatch/CheckPatch.cmake
  )

add_custom_target(checkpatch
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND} -DCHECKPATCH_RUN=1 -P ${CMAKE_SOURCE_DIR}/tools/checkpatch/CheckPatch.cmake
  )

#
# Rules for checking license and copyright headers
#
add_custom_target(checkspdx-codebase
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND} -DCHECKSPDX_CODEBASE=1 -P ${CMAKE_SOURCE_DIR}/tools/checkspdx/CheckSPDX.cmake
  )

add_custom_target(checkspdx-patch
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND} -DCHECKSPDX_PATCH=1 -P ${CMAKE_SOURCE_DIR}/tools/checkspdx/CheckSPDX.cmake
  )

#
# Rules for checking header files include order
#
add_custom_target(checkincludes-codebase
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND} -DCHECKINCLUDES_CODEBASE=1 -P ${CMAKE_SOURCE_DIR}/tools/checkincludes/CheckIncludes.cmake
  )

add_custom_target(checkincludes-patch
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND} -DCHECKINCLUDES_PATCH=1 -P ${CMAKE_SOURCE_DIR}/tools/checkincludes/CheckIncludes.cmake
  )

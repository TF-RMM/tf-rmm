#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

cmake_minimum_required(VERSION 3.20.0)

# allow target_link_libraries() to be used with targets in other directories
cmake_policy(SET CMP0079 NEW)

#
# Add our module search paths so we can `include()` our CMake modules.
#
list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_LIST_DIR}/cmake/Modules")
include(GitUtils)

#
# Include any dependencies.
#
include(ArmConfigOption)
include(ArmConfigOptionOverride)

#
# Update the Submodules
#
Git_Update_Submodule()

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

project(RMM VERSION 0.7.0 LANGUAGES C CXX ASM)

#
# Set global flags.
#

set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED TRUE)
set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED TRUE)
set(CMAKE_C_EXTENSIONS TRUE)

if(RMM_STATIC_ANALYSIS_CPPCHECK)
    set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
endif()

#
# Set march compiler option
#
detect_and_set_march()

#
# Include the platform makefile
#
include("cmake/Platforms.cmake")

#
# Include Coverage report framework
#
include("cmake/CoverageReport.cmake")

#
# Include the Unit Test Framework
#
include(UnitTestFramework)

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
# Recurse into the various component subdirectories
#
add_subdirectory("lib")
add_subdirectory("app")
add_subdirectory("runtime")

if(RMM_DOCS)
    add_subdirectory("docs")
endif()

#
# Copy 'rmm-runtime' executable to 'build/$<CONFIG>/rmm_core.elf'.
#

set(ARTEFACT_DIR "${CMAKE_BINARY_DIR}/$<CONFIG>")
add_custom_command(
    COMMAND ${CMAKE_COMMAND} -E make_directory "${ARTEFACT_DIR}"
    COMMAND "${CMAKE_COMMAND}" -E copy_if_different "$<TARGET_FILE:rmm-runtime>" "${ARTEFACT_DIR}/rmm_core.elf"
    OUTPUT rmm_core.elf
    DEPENDS rmm-runtime)

#
# Create rmm.elf as a copy of rmm_core.elf to keep CI working
#
add_custom_command(
    COMMAND "${CMAKE_COMMAND}" -E copy ${ARTEFACT_DIR}/rmm_core.elf ${ARTEFACT_DIR}/rmm.elf
    OUTPUT rmm.elf
    DEPENDS rmm_core.elf)

#
# Create the flat binary using whatever tool comes with the toolchain.
#

if(CMAKE_OBJCOPY)
    add_custom_command(
        COMMAND "${CMAKE_OBJCOPY}" -O binary "${ARTEFACT_DIR}/rmm_core.elf" "${ARTEFACT_DIR}/rmm_core.img"
        OUTPUT rmm_core.img
        DEPENDS rmm_core.elf)
endif()

#
# Create the dump file using whatever tool comes with the toolchain.
#

if(CMAKE_OBJDUMP)
    add_custom_command(
        COMMAND "${CMAKE_OBJDUMP}" -dxS "${ARTEFACT_DIR}/rmm_core.elf" > "${ARTEFACT_DIR}/rmm_core.dump"
        OUTPUT rmm_core.dump
        DEPENDS rmm_core.elf)
endif()

#
# Copy 'rmm-runtime.map' to 'build/$<CONFIG>/rmm_core.map'
#

add_custom_command(
    COMMAND "${CMAKE_COMMAND}" -E copy_if_different "$<TARGET_FILE:rmm-runtime>.map" "${ARTEFACT_DIR}/rmm_core.map"
    OUTPUT rmm_core.map
    DEPENDS rmm-runtime)

if(NOT RMM_ARCH STREQUAL fake_host)
    set(RMM_IMG "rmm.img")
    find_program(BUNDLE_APP_RMM "bundle_app_rmm.py"
        PATHS ${CMAKE_SOURCE_DIR}
        PATH_SUFFIXES app
        DOC "bundle_app_rmm.py")

    set(BUNDLE_COMMAND_OUTPUT "${ARTEFACT_DIR}/bundle_app_out.txt")
    add_custom_command(
        COMMAND "${BUNDLE_APP_RMM}" --out-bin ${ARTEFACT_DIR}/${RMM_IMG} --rmm-bin ${ARTEFACT_DIR}/rmm_core.img --log-file-name ${BUNDLE_COMMAND_OUTPUT} ${EL0_APP_BIN_LIST}
        OUTPUT ${RMM_IMG}
        DEPENDS rmm_core.img rmm-random-app rmm-attestation-app)
endif()

add_custom_target(rmm ALL DEPENDS rmm_core.img rmm_core.dump rmm_core.elf rmm.elf rmm_core.map ${RMM_IMG} rmm-attestation-app rmm-random-app)

#
# Set up additional tooling.
#

add_subdirectory("tools")

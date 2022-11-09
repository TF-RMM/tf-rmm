#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

find_package(Python3 COMPONENTS Interpreter REQUIRED)

#
# Set up any necessary Mbed TLS configuration options. In the case of an
# inability to build the project with the current set of tools, we allow the
# user to specify an alternative toolchain and generator.
#

arm_config_option(
    NAME MbedTLS_TOOLCHAIN_FILE
    HELP "MbedTLS toolchain file."
    DEFAULT "${CMAKE_TOOLCHAIN_FILE}"
    TYPE FILEPATH
    ADVANCED)

arm_config_option(
    NAME MbedTLS_GENERATOR
    HELP "MbedTLS CMake generator."
    DEFAULT "${CMAKE_GENERATOR}"
    TYPE STRING
    ADVANCED)

arm_config_option(
    NAME MbedTLS_GENERATOR_PLATFORM
    HELP "MbedTLS CMake generator platform."
    DEFAULT "${CMAKE_GENERATOR_PLATFORM}"
    TYPE STRING
    ADVANCED)

arm_config_option(
    NAME MbedTLS_GENERATOR_TOOLSET
    HELP "MbedTLS CMake generator toolset."
    DEFAULT "${CMAKE_GENERATOR_TOOLSET}"
    TYPE STRING
    ADVANCED)

# Set up MbedTLS build type. Default is "Release".
arm_config_option(
    NAME MbedTLS_BUILD_TYPE
    HELP "MbedTLS build type."
    STRINGS "Release" "Debug")

message(STATUS "MbedTLS_BUILD_TYPE set to ${MbedTLS_BUILD_TYPE}")

#
# Set up MbedTLS using our own libc. This is done by getting certain properties
# from our libc target and applying them to MbedTLS - not ideal, but MbedTLS
# doesn't provide an interface library for us to use.
#

get_target_property(system_includes rmm-lib-libc
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES)
get_target_property(includes rmm-lib-libc
    INTERFACE_INCLUDE_DIRECTORIES)
get_target_property(definitions rmm-lib-libc
    INTERFACE_COMPILE_DEFINITIONS)
get_target_property(options rmm-lib-libc
    INTERFACE_COMPILE_OPTIONS)

#
# System include directories appear in both the `SYSTEM_INCLUDE_DIRECTORIES` and
# `INCLUDE_DIRECTORIES` properties, so filter them out of the latter.
#

list(REMOVE_ITEM includes ${system_includes})

#
# Target properties that are not set return `<PROPERTY>-NOTFOUND`. Clear any
# variables where this occurred.
#

foreach(set IN ITEMS system_includes includes definitions options)
    if(NOT ${set})
        set(${set})
    endif()
endforeach()

#
# Add MbedTLS config header file
#

list(APPEND includes "${RMM_SOURCE_DIR}/configs/mbedtls")
list(APPEND definitions "MBEDTLS_CONFIG_FILE=\"<mbedtls_config.h>\"")

#
# Create compiler flags from the libc properties we retrieved.
#

list(TRANSFORM system_includes PREPEND "-isystem ")
list(TRANSFORM includes PREPEND "-I ")
list(TRANSFORM definitions PREPEND "-D ")

foreach(set IN ITEMS system_includes includes definitions options)
    string(REPLACE ";" " " ${set} "${${set}}")
endforeach()

string(PREPEND MbedTLS_C_FLAGS "${definitions} ")
string(PREPEND MbedTLS_C_FLAGS "${system_includes} ")
string(PREPEND MbedTLS_C_FLAGS "${includes} ")
string(PREPEND MbedTLS_C_FLAGS "${options} ")

#
# Unmark some of these configuration options as advanced, in case building fails
# in the next step and we want to re-expose them to the user.
#

mark_as_advanced(CLEAR MbedTLS_TOOLCHAIN_FILE)
mark_as_advanced(CLEAR MbedTLS_GENERATOR)
mark_as_advanced(CLEAR MbedTLS_GENERATOR_PLATFORM)
mark_as_advanced(CLEAR MbedTLS_GENERATOR_TOOLSET)
mark_as_advanced(CLEAR MbedTLS_C_FLAGS)

#
# Set up the source, binary and install directories.
#

set(MbedTLS_SOURCE_DIR "${RMM_SOURCE_DIR}/ext/mbedtls")
set(MbedTLS_INSTALL_DIR "${RMM_BINARY_DIR}/ext/mbedtls")
set(MbedTLS_BINARY_DIR "${MbedTLS_INSTALL_DIR}${CMAKE_FILES_DIRECTORY}")

#
# Detect whether we need to reconfigure the CMake cache from the very start,
# which we need to do if the user has modified certain one-shot options.
#

if(MbedTLS_TOOLCHAIN_FILE_CHANGED OR
   MbedTLS_BUILD_TYPE_CHANGED OR
   MbedTLS_GENERATOR_CHANGED OR
   MbedTLS_GENERATOR_PLATFORM_CHANGED OR
   MbedTLS_GENERATOR_TOOLSET_CHANGED)
    file(REMOVE "${MbedTLS_BINARY_DIR}/CMakeCache.txt")
endif()

#
# Configure, build and install the CMake project.
#

unset(mbedtls_configure)

list(APPEND mbedtls_configure -G "${MbedTLS_GENERATOR}")
list(APPEND mbedtls_configure -S "${MbedTLS_SOURCE_DIR}")
list(APPEND mbedtls_configure -B "${MbedTLS_BINARY_DIR}")

if(MbedTLS_GENERATOR_PLATFORM)
    list(APPEND mbedtls_configure -A "${MbedTLS_GENERATOR_PLATFORM}")
endif()

if(MbedTLS_GENERATOR_TOOLSET)
    list(APPEND mbedtls_configure -T "${MbedTLS_GENERATOR_TOOLSET}")
endif()

list(APPEND mbedtls_configure -D "CMAKE_INSTALL_PREFIX=${MbedTLS_INSTALL_DIR}")
list(APPEND mbedtls_configure -D "CMAKE_TOOLCHAIN_FILE=${MbedTLS_TOOLCHAIN_FILE}")
list(APPEND mbedtls_configure -D "ENABLE_PROGRAMS=NO")
list(APPEND mbedtls_configure -D "ENABLE_TESTING=NO")
list(APPEND mbedtls_configure -D "CMAKE_C_COMPILER_WORKS=1")
if(CMAKE_VERBOSE_MAKEFILE)
    list(APPEND mbedtls_configure -D "CMAKE_VERBOSE_MAKEFILE=1")
endif()

#
# Mbed TLS's build system ignores and overwrites the flags we specify in our
# toolchain files. Un-overwrite them, because they're there for a good reason.
#

string(TOUPPER ${MbedTLS_BUILD_TYPE} build_type)

if(RMM_FPU_USE_AT_REL2)
    # Enable using floating point registers for mbed TLS
    string(REPLACE "-mgeneral-regs-only" "" FP_CMAKE_C_FLAGS ${CMAKE_C_FLAGS})
    # Enable using crypto and sha instructions
    string(REGEX REPLACE "(march=[^\\ ]*)" "\\1+sha3+crypto" FP_CMAKE_C_FLAGS ${FP_CMAKE_C_FLAGS})
    # Enable using SHA256 and SHA512 instructions in MbedTLS
    string(APPEND FP_CMAKE_C_FLAGS
            " -DMBEDTLS_SHA256_USE_A64_CRYPTO_ONLY=1 "
            " -DMBEDTLS_SHA512_USE_A64_CRYPTO_ONLY=1 ")
else()
    set(FP_CMAKE_C_FLAGS ${CMAKE_C_FLAGS})
endif()

list(APPEND mbedtls_configure
    -D "CMAKE_C_FLAGS=${FP_CMAKE_C_FLAGS} ${CMAKE_C_FLAGS_${build_type}} ${MbedTLS_C_FLAGS}")

execute_process(
    COMMAND "${CMAKE_COMMAND}"
        ${mbedtls_configure})

execute_process(
    COMMAND "${CMAKE_COMMAND}"
        --build "${MbedTLS_BINARY_DIR}"
        --config "${MbedTLS_BUILD_TYPE}")

execute_process(
    COMMAND "${CMAKE_COMMAND}"
        --install "${MbedTLS_BINARY_DIR}"
        --config "${MbedTLS_BUILD_TYPE}")

#
# Mark some of the configuration options as advanced if building succeeded.
#

mark_as_advanced(FORCE MbedTLS_TOOLCHAIN_FILE)
mark_as_advanced(FORCE MbedTLS_GENERATOR)
mark_as_advanced(FORCE MbedTLS_GENERATOR_PLATFORM)
mark_as_advanced(FORCE MbedTLS_GENERATOR_TOOLSET)

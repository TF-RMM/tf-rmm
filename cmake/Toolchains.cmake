#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Set up the toolchain logic. This is only necessary if a toolchain file hasn't
# been provided. Otherwise, we force this option to an empty string.
#

if(DEFINED CACHE{CMAKE_TOOLCHAIN_FILE} AND NOT DEFINED RMM_TOOLCHAIN)
    message(WARNING
        "The RMM project does not support `CMAKE_TOOLCHAIN_FILE` directly. "
        "Please use `RMM_TOOLCHAIN` to configure your desired toolchain.")

    unset(CMAKE_TOOLCHAIN_FILE CACHE)
endif()

file(GLOB toolchains
    RELATIVE "${CMAKE_SOURCE_DIR}/toolchains/${RMM_ARCH}"
        "${CMAKE_SOURCE_DIR}/toolchains/${RMM_ARCH}/*.cmake")
string(REPLACE ".cmake" "" toolchains "${toolchains}")

arm_config_option(
    NAME RMM_TOOLCHAIN
    HELP "Toolchain name."
    STRINGS ${toolchains}
    DEFAULT ""
    DEPENDS (NOT RMM_TOOLCHAIN IN_LIST toolchains)
    ELSE "${RMM_TOOLCHAIN}")

if(NOT EXISTS CMAKE_TOOLCHAIN_FILE)
    set(CMAKE_TOOLCHAIN_FILE
        "${CMAKE_SOURCE_DIR}/toolchains/${RMM_ARCH}/${RMM_TOOLCHAIN}.cmake")
endif()

#
# Configure whether UBSAN should be enabled for the build.
# Default is false.
# This option is deprecated in favor of RMM_SANITIZERS,
# which provides a more flexible way to configure sanitizers.
arm_config_option(
        NAME UBSAN
        HELP "Enable Undefined Behavior Sanitizer."
        BOOL
        DEFAULT OFF
)

#
# Configure which sanitizers should be enabled for the build.
# Accepts a comma, pipe, plus, or semicolon separated list of:
#   ALL   - Enable all sanitizers below (case-insensitive)
#   UBSAN - Undefined Behavior Sanitizer
#   ICSAN - Implicit Conversion Sanitizer (LLVM only)
#   LBSAN - Local Bounds Sanitizer (LLVM only)
#   NGSAN - Nullability Group Sanitizer (LLVM only)
# Using LLVM-only sanitizers with a non-LLVM toolchain is a fatal error.
# Default is empty (no sanitizers).
# Example: -DRMM_SANITIZERS="UBSAN,ICSAN"
# Example: -DRMM_SANITIZERS="ALL"
#
arm_config_option(
    NAME RMM_SANITIZERS
    HELP "Sanitizers to enable: ALL, UBSAN, ICSAN, LBSAN, NGSAN (separated by , | + or ;)"
    TYPE STRING
    DEFAULT "")

# Normalize alternative separators to CMake list separator
string(REPLACE "," ";" RMM_SANITIZERS "${RMM_SANITIZERS}")
string(REPLACE "|" ";" RMM_SANITIZERS "${RMM_SANITIZERS}")
string(REPLACE "+" ";" RMM_SANITIZERS "${RMM_SANITIZERS}")
string(REPLACE " " "" RMM_SANITIZERS "${RMM_SANITIZERS}")

# Case-insensitive normalisation and "ALL" expansion
set(_valid_sanitizers UBSAN ICSAN LBSAN NGSAN)
set(_normalized_sanitizers "")
foreach(_san IN LISTS RMM_SANITIZERS)
    string(TOUPPER "${_san}" _san_upper)
    if(_san_upper STREQUAL "ALL")
        set(_normalized_sanitizers ${_valid_sanitizers})
        break()
    endif()
    list(APPEND _normalized_sanitizers "${_san_upper}")
endforeach()
set(RMM_SANITIZERS "${_normalized_sanitizers}")

# Validate entries
foreach(_san IN LISTS RMM_SANITIZERS)
    if(NOT _san IN_LIST _valid_sanitizers)
        message(FATAL_ERROR
            "Unknown sanitizer '${_san}' in RMM_SANITIZERS. "
            "Valid values: ALL, UBSAN, ICSAN, LBSAN, NGSAN")
    endif()
endforeach()

# Check toolchain compatibility for LLVM-only sanitizers.
set(_llvm_only_sanitizers ICSAN LBSAN NGSAN)
if(RMM_SANITIZERS)
    string(TOLOWER "${RMM_TOOLCHAIN}" _toolchain_lower)
    if(_toolchain_lower STREQUAL "llvm")
        # LLVM toolchain: all sanitizers are supported, nothing to do.
    else()
        # Non-LLVM toolchain: check for any LLVM-only sanitizers.
        foreach(_san IN LISTS _llvm_only_sanitizers)
            if(_san IN_LIST RMM_SANITIZERS)
                message(FATAL_ERROR
                    "Sanitizer '${_san}' is only supported with the LLVM toolchain,"
                    " but RMM_TOOLCHAIN='${RMM_TOOLCHAIN}' was selected.")
            endif()
        endforeach()
    endif()
endif()

# Derive individual cache variables so toolchain files and Sanitizers.cmake
# can continue to use them unchanged.
foreach(_san IN LISTS _valid_sanitizers)
    if(_san IN_LIST RMM_SANITIZERS)
        set(${_san} ON  CACHE BOOL "Derived from RMM_SANITIZERS" FORCE)
    else()
        set(${_san} OFF CACHE BOOL "Derived from RMM_SANITIZERS" FORCE)
    endif()
endforeach()

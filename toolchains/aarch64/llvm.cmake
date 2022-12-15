#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

include_guard()

include(${CMAKE_CURRENT_LIST_DIR}/common_aarch64.cmake)

set(CMAKE_TRY_COMPILE_TARGET_TYPE STATIC_LIBRARY)

find_program(CMAKE_C_COMPILER
    NAMES "clang"
    DOC "Path to clang."
    REQUIRED)

set(CMAKE_ASM_COMPILER ${CMAKE_C_COMPILER})

find_program(CMAKE_OBJCOPY
    NAMES "llvm-objcopy"
    DOC "Path to llvm-objcopy."
    REQUIRED)

find_program(CMAKE_OBJDUMP
    NAMES "llvm-objdump"
    DOC "Path to llvm-objcopy."
    REQUIRED)

find_program(CMAKE_AR
    NAMES "llvm-ar"
    DOC "Path to llvm-ar."
    REQUIRED)

find_program(CMAKE_RANLIB
    NAMES "llvm-ranlib"
    DOC "Path to llvm-ranlib."
    REQUIRED)

# Find the path to AArch64 gcc
find_program(A64_GCC
    NAMES "$ENV{CROSS_COMPILE}gcc"
    DOC "Path to aarch64 gcc"
    REQUIRED)

# Get the AArch64 GCC triplet
execute_process(COMMAND ${A64_GCC} -dumpmachine
    OUTPUT_VARIABLE A64-GCC-TRIPLET
    OUTPUT_STRIP_TRAILING_WHITESPACE)

# Construct the path to `include` folder of AArch64 GCC toolchain
get_filename_component(A64_GCC_DIR ${A64_GCC} DIRECTORY)
set(A64_GCC_INC_DIR "${A64_GCC_DIR}/../${A64-GCC-TRIPLET}/include")
message(STATUS "Using ${A64_GCC_INC_DIR} for std include headers")

foreach(language IN ITEMS ASM C)
    set(CMAKE_${language}_COMPILER_TARGET "${A64-GCC-TRIPLET}")
    string(APPEND CMAKE_${language}_STANDARD_INCLUDE_DIRECTORIES "${A64_GCC_INC_DIR}")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-Wno-unknown-warning-option ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-Wno-unused-function ")

    # Avoid warning for -mbranch-protection option not being recognized by clang during link phase.
    string(APPEND CMAKE_${language}_FLAGS_INIT "-Wno-unused-command-line-argument ")
endforeach()

# Use lld as default linker
string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-fuse-ld=lld ")

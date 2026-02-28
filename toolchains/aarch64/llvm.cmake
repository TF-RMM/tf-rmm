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
    OUTPUT_VARIABLE A64_GCC_TRIPLET
    OUTPUT_STRIP_TRAILING_WHITESPACE)

# Get the path to the glibc headers used by AArch64 gcc
file(WRITE "${CMAKE_BINARY_DIR}/test_include.c" "#include <assert.h>\n")
execute_process(
    COMMAND ${A64_GCC} -E -xc ${CMAKE_BINARY_DIR}/test_include.c
    OUTPUT_VARIABLE PREPROCESS_OUTPUT
)
file(REMOVE "${CMAKE_BINARY_DIR}/test_include.c")

# Parse the preprocessor output to find assert.h path
string(REGEX MATCH "# [0-9]+ \"([^\"]*assert\\.h)\"" ASSERT_MATCH "${PREPROCESS_OUTPUT}")
set(GLIBC_HEADER_PATH "${CMAKE_MATCH_1}")

# Extract the directory path from the full file path
get_filename_component(A64_GCC_INC_DIR "${GLIBC_HEADER_PATH}" DIRECTORY)
message(STATUS "Using ${A64_GCC_INC_DIR} for std include headers")

foreach(language IN ITEMS ASM C)
    set(CMAKE_${language}_COMPILER_TARGET "${A64_GCC_TRIPLET}")
    string(APPEND CMAKE_${language}_STANDARD_INCLUDE_DIRECTORIES "${A64_GCC_INC_DIR}")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-Wno-unknown-warning-option ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-Wno-unused-function ")

    # Avoid warning for -mbranch-protection option not being recognized by clang during link phase.
    string(APPEND CMAKE_${language}_FLAGS_INIT "-Wno-unused-command-line-argument ")
endforeach()

# Use lld as default linker
string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-fuse-ld=lld ")
string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-Wl,--apply-dynamic-relocs ")

if (ICSAN)
    string(APPEND CMAKE_C_FLAGS_INIT "-fsanitize-trap=implicit-conversion ")
    string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-fsanitize-trap=implicit-conversion ")
endif()

if (LBSAN)
    string(APPEND CMAKE_C_FLAGS_INIT "-fsanitize-trap=local-bounds ")
    string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-fsanitize-trap=local-bounds ")
endif()

if (NGSAN)
    string(APPEND CMAKE_C_FLAGS_INIT "-fsanitize-trap=nullability ")
    string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-fsanitize-trap=nullability ")
endif()

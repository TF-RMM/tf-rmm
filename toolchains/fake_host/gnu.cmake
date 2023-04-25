#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

include_guard()

include(${CMAKE_CURRENT_LIST_DIR}/common_fake_host.cmake)

find_program(CMAKE_C_COMPILER
    NAMES "gcc"
    DOC "Path to gcc."
    REQUIRED)

#
# Needed to build CppUTest for unit tests
#
find_program(CMAKE_CXX_COMPILER
    NAMES "g++"
    DOC "Path to g++."
    REQUIRED)

set(CMAKE_ASM_COMPILER ${CMAKE_C_COMPILER})

string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-Wl,--build-id=none ")

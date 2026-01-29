#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

include_guard()

include(${CMAKE_CURRENT_LIST_DIR}/common_fake_host.cmake)

find_program(CMAKE_C_COMPILER
        NAMES "afl-gcc-fast"
        DOC "Path to AFL gcc compiler."
        REQUIRED)

find_program(CMAKE_CXX_COMPILER
        NAMES "afl-g++-fast"
        DOC "Path to AFL g++ compiler."
        REQUIRED)

set(CMAKE_ASM_COMPILER ${CMAKE_C_COMPILER})

string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-Wl,--build-id=none ")

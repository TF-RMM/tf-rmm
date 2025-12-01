#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

include_guard()

include(${CMAKE_CURRENT_LIST_DIR}/common_fake_host.cmake)

find_program(CMAKE_C_COMPILER
    NAMES "clang"
    DOC "Path to clang."
    REQUIRED)

find_program(CMAKE_CXX_COMPILER
    NAMES "clang++"
    DOC "Path to clang++."
    REQUIRED)

set(CMAKE_ASM_COMPILER ${CMAKE_C_COMPILER})

foreach(language IN ITEMS ASM C CXX)
    string(APPEND CMAKE_${language}_FLAGS_INIT "-Wno-unknown-warning-option ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-Wno-unused-function ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-Wno-c99-designator ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-fPIC ")
endforeach()

string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-Wl,--build-id=none ")
string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-fuse-ld=lld ")

if (ICSAN)
    string(APPEND CMAKE_C_FLAGS_INIT "-fno-sanitize-recover=implicit-conversion ")
    string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-fno-sanitize-recover=implicit-conversion ")
endif()

if (LBSAN)
    string(APPEND CMAKE_C_FLAGS_INIT "-fno-sanitize-recover=local-bounds ")
    string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-fno-sanitize-recover=local-bounds ")
endif()

if (NGSAN)
    string(APPEND CMAKE_C_FLAGS_INIT "-fno-sanitize-recover=nullability ")
    string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-fno-sanitize-recover=nullability ")
endif()

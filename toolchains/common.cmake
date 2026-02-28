#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

include_guard()

set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_PACKAGE ONLY)

foreach(language IN ITEMS ASM C CXX)
    string(APPEND CMAKE_${language}_FLAGS_INIT "-fno-common ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-ffunction-sections ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-fdata-sections ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-fno-delete-null-pointer-checks ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-Wall -Werror -Wstrict-overflow ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-Wextra -Wno-implicit-fallthrough ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-gdwarf-4 ")
    string(APPEND CMAKE_${language}_FLAGS_DEBUG_INIT "-Og -Wnull-dereference -Wstrict-aliasing=1 ")
    string(APPEND CMAKE_${language}_FLAGS_RELEASE_INIT "-g ")
endforeach()

string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-Wl,--gc-sections -g ")

if (UBSAN)
    string(APPEND CMAKE_C_FLAGS_INIT "-fsanitize=undefined ")
    string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-fsanitize=undefined ")
endif()

if (ICSAN)
    string(APPEND CMAKE_C_FLAGS_INIT "-fsanitize=implicit-conversion ")
    string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-fsanitize=implicit-conversion ")
endif()

if (LBSAN)
    string(APPEND CMAKE_C_FLAGS_INIT "-fsanitize=local-bounds ")
    string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-fsanitize=local-bounds ")
endif()

if (NGSAN)
    string(APPEND CMAKE_C_FLAGS_INIT "-fsanitize=nullability ")
    string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-fsanitize=nullability ")
endif()

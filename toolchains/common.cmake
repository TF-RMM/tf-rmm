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
    string(APPEND CMAKE_${language}_FLAGS_INIT "-Wno-type-limits ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-gdwarf-4 ")
    string(APPEND CMAKE_${language}_FLAGS_INIT "-D_FORTIFY_SOURCE=2 ")
    string(APPEND CMAKE_${language}_FLAGS_DEBUG_INIT "-Og -Wnull-dereference -Wstrict-aliasing=1 ")
    string(APPEND CMAKE_${language}_FLAGS_RELEASE_INIT "-g ")
endforeach()

string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-Wl,--gc-sections -g ")

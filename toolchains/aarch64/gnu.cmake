#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

include_guard()

include(${CMAKE_CURRENT_LIST_DIR}/common_aarch64.cmake)

find_program(CMAKE_ASM_COMPILER
    NAMES "$ENV{CROSS_COMPILE}gcc"
    DOC "Path to an aarch64 compiler."
    REQUIRED)

find_program(CMAKE_C_COMPILER
    NAMES "$ENV{CROSS_COMPILE}gcc"
    DOC "Path to an aarch64 compiler."
    REQUIRED)

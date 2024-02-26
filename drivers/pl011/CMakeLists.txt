#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-driver-pl011)

target_link_libraries(rmm-driver-pl011
    PRIVATE rmm-lib)

target_include_directories(rmm-driver-pl011
    PUBLIC "include")

target_sources(rmm-driver-pl011
    PRIVATE "src/pl011.c")

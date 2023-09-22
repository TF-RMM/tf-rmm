#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-measurement)

target_link_libraries(rmm-lib-measurement
    PUBLIC rmm-mbedtls
           rmm-lib-smc
    PRIVATE rmm-lib-arch
            rmm-lib-common
            rmm-lib-debug)

target_include_directories(rmm-lib-measurement
    PUBLIC "include")

target_sources(rmm-lib-measurement
    PRIVATE
        "src/measurement.c"
        "src/rim.c")

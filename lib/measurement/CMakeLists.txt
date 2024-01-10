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
    PUBLIC "include"
    PRIVATE "src")

if(HOST_VARIANT STREQUAL "host_cbmc")
    target_sources(rmm-lib-measurement
       PRIVATE "src/fake_host/cbmc_rim.c")
    # In case of 'host_cbmc' variant no further source files are added to
    # the build.
    return()
endif()

target_sources(rmm-lib-measurement
    PRIVATE
        "src/measurement.c"
        "src/rim.c")

#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-timers)

target_link_libraries(rmm-lib-timers
    PRIVATE rmm-lib-arch
            rmm-lib-attestation
            rmm-lib-common
            rmm-lib-gic
            rmm-lib-measurement
            rmm-lib-realm
            rmm-lib-smc
            rmm-lib-debug
            rmm-lib-xlat)

target_include_directories(rmm-lib-timers
    PUBLIC "include")

target_sources(rmm-lib-timers
    PRIVATE "src/timers.c")

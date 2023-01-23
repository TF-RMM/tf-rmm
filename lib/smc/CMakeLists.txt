#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-smc)

target_link_libraries(rmm-lib-smc
    PRIVATE rmm-lib-arch
            rmm-lib-common)

target_include_directories(rmm-lib-smc
    PUBLIC "include")

if(NOT RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-lib-smc
        PRIVATE "src/aarch64/smc.S"
                "src/smc-rmi-offsets.c"
                "src/smc-rsi-offsets.c")
else()
    target_sources(rmm-lib-smc
        PRIVATE "src/fake_host/smc_wrapper.c")
endif()

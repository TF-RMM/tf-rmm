#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-plat-host_fuzz)

target_link_libraries(rmm-plat-host_fuzz
    PRIVATE rmm-lib
            rmm-el2-stub
            rmm-host-harness)

target_sources(rmm-plat-host_fuzz
    PRIVATE "src/host_setup.c"
            "src/host_harness.c")

target_include_directories(rmm-plat-host_fuzz
    PUBLIC "include")

# Export symbols for backtrace_symbols_fd() in the crash signal handler
target_link_options(rmm-plat-host_fuzz
    INTERFACE -rdynamic)

add_library(rmm-platform ALIAS rmm-plat-host_fuzz)

#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# This layer implement APIs from host_utils.h and host_harness.h which
# is used by both apps at el0 and RMM core at el2.
#
add_library(rmm-host-el2-el0-cmn)

target_link_libraries(rmm-host-el2-el0-cmn
    PRIVATE
        rmm-common
        rmm-lib-arch
        rmm-lib-common
        rmm-lib-debug)

target_sources(rmm-host-el2-el0-cmn
    PRIVATE "src/host_spinlock.c"
            "src/host_sysregs.c")

# Include headers from harness without link dependency.
target_include_directories(rmm-host-el2-el0-cmn
    PRIVATE "src"
            "../harness/include")

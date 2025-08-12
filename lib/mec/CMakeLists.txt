#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-mec)

target_link_libraries(rmm-lib-mec
    PRIVATE rmm-lib-debug
            rmm-lib-rmm_el3_ifc
            rmm-lib-smc
    PUBLIC  rmm-lib-arch
)

target_include_directories(rmm-lib-mec
    PUBLIC  "include"
)

target_sources(rmm-lib-mec
        PRIVATE "src/mec.c")

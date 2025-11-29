#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-smmuv3)

target_link_libraries(rmm-lib-smmuv3
    PRIVATE rmm-lib)

target_include_directories(rmm-lib-smmuv3
    PUBLIC "include"
    PRIVATE "src/${RMM_ARCH}")

target_sources(rmm-lib-smmuv3
    PRIVATE "src/${RMM_ARCH}/smmuv3.c")

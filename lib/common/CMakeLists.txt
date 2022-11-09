#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-common INTERFACE)

target_include_directories(rmm-lib-common
    INTERFACE "include"
    INTERFACE "include/${RMM_ARCH}")

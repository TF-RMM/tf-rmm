#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-app-cmn-fw)

target_link_libraries(rmm-app-cmn-fw
    PRIVATE
        rmm-lib-arch
        rmm-lib-console
        rmm-lib-slot_buf)

target_include_directories(rmm-app-cmn-fw
    PRIVATE "src"
    PUBLIC "include"
           "include/${RMM_ARCH}")

target_sources(rmm-app-cmn-fw
    PRIVATE
        "src/${RMM_ARCH}/app_header.c"
    )

list(APPEND RMM_EL2_STUB_LIBRARIES "rmm-app-cmn-fw")
set(RMM_EL2_STUB_LIBRARIES ${RMM_EL2_STUB_LIBRARIES} PARENT_SCOPE)

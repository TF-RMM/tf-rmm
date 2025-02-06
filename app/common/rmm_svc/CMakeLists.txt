#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-app-cmn-svc)

target_link_libraries(rmm-app-cmn-svc
    PRIVATE
        rmm-lib-arch
        rmm-lib-console
        rmm-lib-debug
        rmm-lib-rmm_el3_ifc
        rmm-lib-slot_buf
        rmm-lib-xlat
        rmm-el2-stub)

target_include_directories(rmm-app-cmn-svc
    PUBLIC "include"
    PUBLIC "../../common/include")

target_sources(rmm-app-cmn-svc
    PRIVATE "src/app_services.c"
    )

list(APPEND RMM_EL2_STUB_LIBRARIES "rmm-app-cmn-svc")
set(RMM_EL2_STUB_LIBRARIES ${RMM_EL2_STUB_LIBRARIES} PARENT_SCOPE)

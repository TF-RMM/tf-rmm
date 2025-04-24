#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-app-dev-assign-stub)

target_link_libraries(rmm-app-dev-assign-stub
    PRIVATE
    rmm-el2-stub
    rmm-lib-arch
    rmm-lib-common
    rmm-lib-debug)

target_include_directories(rmm-app-dev-assign-stub
    PUBLIC "include"
    PRIVATE "../../common/include")

target_sources(rmm-app-dev-assign-stub
        PRIVATE "src/dev_assign_app_stub.c")

list(APPEND RMM_EL2_STUB_LIBRARIES "rmm-app-dev-assign-stub")
set(RMM_EL2_STUB_LIBRARIES ${RMM_EL2_STUB_LIBRARIES} PARENT_SCOPE)

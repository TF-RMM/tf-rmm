#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-app-random-stub)

target_link_libraries(rmm-app-random-stub
    rmm-el2-stub
    rmm-lib-arch
    rmm-lib-common
    rmm-lib-debug)

target_include_directories(rmm-app-random-stub
    PUBLIC "include"
    PRIVATE "../../common/include")

if((HOST_VARIANT STREQUAL "host_cbmc") OR (HOST_VARIANT STREQUAL "host_test"))
    target_sources(rmm-app-random-stub
        PRIVATE "src/no_app_support/random_app.c"
        )
else()
    target_sources(rmm-app-random-stub
        PRIVATE "src/app_support/random_app.c"
        )
endif()

list(APPEND RMM_EL2_STUB_LIBRARIES "rmm-app-random-stub")
set(RMM_EL2_STUB_LIBRARIES ${RMM_EL2_STUB_LIBRARIES} PARENT_SCOPE)

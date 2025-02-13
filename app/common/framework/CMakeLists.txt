#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-app-cmn-fw)

target_link_libraries(rmm-app-cmn-fw
    PRIVATE
        rmm-lib-arch
        rmm-lib-debug
        rmm-lib-console
        rmm-lib-slot_buf
        rmm-el2-stub
        rmm-lib-xlat)

target_include_directories(rmm-app-cmn-fw
    PRIVATE "src"
    PUBLIC "include"
           "include/${RMM_ARCH}"
           "../include/${RMM_ARCH}"
           "../../common/include")

if((HOST_VARIANT STREQUAL "host_cbmc") OR (HOST_VARIANT STREQUAL "host_test"))
    target_sources(rmm-app-cmn-fw
        PRIVATE "src/no_app_support/app.c"
                "src/no_app_support/app_header.c"
        )
else()
    target_sources(rmm-app-cmn-fw
        PRIVATE "src/${RMM_ARCH}/app.c"
                "src/${RMM_ARCH}/app_header.c"
        )
endif()

target_compile_definitions(rmm-app-cmn-fw
    PUBLIC
        "ATTEST_EL3_TOKEN_SIGN=$<IF:$<BOOL:${ATTEST_EL3_TOKEN_SIGN}>,1,0>"
)

if (NOT RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-app-cmn-fw
        PRIVATE "src/${RMM_ARCH}/app-asm.S")
endif()

list(APPEND RMM_EL2_STUB_LIBRARIES "rmm-app-cmn-fw")
set(RMM_EL2_STUB_LIBRARIES ${RMM_EL2_STUB_LIBRARIES} PARENT_SCOPE)

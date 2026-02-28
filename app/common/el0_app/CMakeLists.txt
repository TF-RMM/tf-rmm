#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

if(HOST_VARIANT STREQUAL "host_cbmc")
    return()
endif()

add_library(rmm-app-common-el0_app)

target_link_libraries(rmm-app-common-el0_app
  PRIVATE
  rmm-lib-console
  rmm-lib-common
  rmm-lib-debug
  rmm-lib-stack_protector
)

target_include_directories(rmm-app-common-el0_app
  PUBLIC "include"
         "include/${RMM_ARCH}"
         "../../common/include"
         "../../common/include/${RMM_ARCH}")

target_sources(rmm-app-common-el0_app
  PRIVATE
    "src/el0_app_helpers.c"
    "src/${RMM_ARCH}/el0_app_arch.c")

target_compile_definitions(rmm-app-common-el0_app
    PUBLIC
        "ATTEST_EL3_TOKEN_SIGN=$<IF:$<BOOL:${ATTEST_EL3_TOKEN_SIGN}>,1,0>"
)

if (RMM_ARCH STREQUAL fake_host)
    target_link_libraries(rmm-app-common-el0_app
        PRIVATE pthread)
else()
    target_sources(rmm-app-common-el0_app
        PRIVATE "src/${RMM_ARCH}/el0_app_helpers.S")
endif()

#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-app-attestation-stub)

target_link_libraries(rmm-app-attestation-stub
    rmm-lib-arch
    rmm-lib-common
    rmm-lib-debug
    rmm-lib-smc
    rmm-el2-stub)

target_include_directories(rmm-app-attestation-stub
    PUBLIC "include"
    PRIVATE "../../common/include")

target_sources(rmm-app-attestation-stub
    PRIVATE
        "src/attest.c")

if (ATTEST_EL3_TOKEN_SIGN)
    target_sources(rmm-app-attestation-stub
        PRIVATE
        "src/attestation_el3_token_sign.c")
endif()

list(APPEND RMM_EL2_STUB_LIBRARIES "rmm-app-attestation-stub")
set(RMM_EL2_STUB_LIBRARIES ${RMM_EL2_STUB_LIBRARIES} PARENT_SCOPE)

#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-app-attestation-stub)

target_link_libraries(rmm-app-attestation-stub
    rmm-lib-smc
    rmm-el2-stub)

target_include_directories(rmm-app-attestation-stub
    PUBLIC "include"
    PRIVATE "../../common/include")

target_sources(rmm-app-attestation-stub
    PRIVATE
        "src/attest.c")

list(APPEND RMM_EL2_STUB_LIBRARIES "rmm-app-attestation-stub")
set(RMM_EL2_STUB_LIBRARIES ${RMM_EL2_STUB_LIBRARIES} PARENT_SCOPE)

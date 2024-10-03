#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# The t_cose library is not included in the CBMC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    add_library(t_cose INTERFACE)
    return()
endif()

add_library(t_cose)

set(T_COSE_SOURCE_DIR "${RMM_SOURCE_DIR}/ext/t_cose")

# Patch t_cose
set(T_COSE_PATCH_DIR "${RMM_SOURCE_DIR}/configs/t_cose")
set(T_COSE_PATCH_FILES
    "${T_COSE_PATCH_DIR}/0001-Add-t_cose_key_encode-API.patch"
    "${T_COSE_PATCH_DIR}/0001-Add-compile-time-option-for-el3-signing.patch")

Git_Apply_Patches(${T_COSE_SOURCE_DIR} "${T_COSE_PATCH_FILES}")

#TODO: Eliminate warning suppression once the t_cose submodule is updated to
#      a released version.
target_compile_options(t_cose
    PRIVATE
        "-Wno-maybe-uninitialized"
        "-Wno-cpp"
        "-Wno-unused-variable")

target_compile_definitions(t_cose
     PUBLIC
         "ATTEST_EL3_TOKEN_SIGN=$<IF:$<BOOL:${ATTEST_EL3_TOKEN_SIGN}>,1,0>"
     PRIVATE
         "T_COSE_USE_PSA_CRYPTO=1"
         "T_COSE_DISABLE_HPKE=1"
)

target_link_libraries(t_cose
    PRIVATE
        rmm-lib-common
        rmm-lib-libc
)

target_link_libraries(t_cose
    PUBLIC
       rmm-mbedtls
       qcbor
)

target_include_directories(t_cose
    PUBLIC
        "include"
        "${T_COSE_SOURCE_DIR}/inc"
        "${T_COSE_SOURCE_DIR}/crypto_adapters"
    PRIVATE
        "${T_COSE_SOURCE_DIR}/src"
)

target_sources(t_cose
    PRIVATE
        "${T_COSE_SOURCE_DIR}/crypto_adapters/t_cose_psa_crypto.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_parameters.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_sign_sign.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_signature_sign_restart.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_util.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_key.c"
)

if (ATTEST_EL3_TOKEN_SIGN)
    target_compile_definitions(t_cose
        PRIVATE
            "T_COSE_DISABLE_COSE_SIGN=1")

    target_sources(t_cose
        PRIVATE
            "src/t_cose_el3_token_sign.c")

    target_link_libraries(t_cose
        PRIVATE
            rmm-lib-arch
            rmm-lib-debug)
endif()

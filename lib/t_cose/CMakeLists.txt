#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(t_cose)

set(T_COSE_SOURCE_DIR "${RMM_SOURCE_DIR}/ext/t_cose")

target_compile_definitions(t_cose
     PUBLIC
         "T_COSE_USE_MBEDTLS_CRYPTO"
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
        "${T_COSE_SOURCE_DIR}/inc"
    PRIVATE
        "${T_COSE_SOURCE_DIR}/src"
)

target_sources(t_cose
    PRIVATE
        "${T_COSE_SOURCE_DIR}/src/t_cose_parameters.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_sign1_sign.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_sign1_verify.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_util.c"
        "${T_COSE_SOURCE_DIR}/crypto_adapters/t_cose_mbedtls_crypto.c"
)

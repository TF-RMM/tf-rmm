#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(t_cose)

set(T_COSE_SOURCE_DIR "${RMM_SOURCE_DIR}/ext/t_cose")

target_compile_definitions(t_cose
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
        "${T_COSE_SOURCE_DIR}/inc"
        "${T_COSE_SOURCE_DIR}/crypto_adapters"
    PRIVATE
        "${T_COSE_SOURCE_DIR}/src"
)

target_sources(t_cose
    PRIVATE
        "${T_COSE_SOURCE_DIR}/src/t_cose_sign1_sign.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_parameters.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_sign1_verify.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_util.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_key.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_sign_sign.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_mac_compute.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_signature_sign_main.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_signature_sign_eddsa.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_sign_verify.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_mac_validate.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_signature_verify_main.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_signature_verify_eddsa.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_encrypt_enc.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_encrypt_dec.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_recipient_dec_keywrap.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_recipient_enc_keywrap.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_recipient_dec_hpke.c"
        "${T_COSE_SOURCE_DIR}/src/t_cose_recipient_enc_hpke.c"
        "${T_COSE_SOURCE_DIR}/src/hpke.c"
        "${T_COSE_SOURCE_DIR}/crypto_adapters/t_cose_psa_crypto.c"
)

#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-attestation)

arm_config_option(
    NAME MBEDTLS_ECP_MAX_OPS
    HELP "Set the number of max operations per ECC signing iteration [0..PSA_INTERRUPTIBLE_MAX_OPS_UNLIMITED]"
    TYPE STRING
    DEFAULT 1000
    ADVANCED)

target_compile_definitions(rmm-lib-attestation
    PRIVATE "MBEDTLS_ECP_MAX_OPS=${MBEDTLS_ECP_MAX_OPS}U")

target_link_libraries(rmm-lib-attestation
  PRIVATE
    rmm-lib-arch
    rmm-lib-debug
    rmm-lib-common
    rmm-lib-libc
    rmm-lib-rmm_el3_ifc
    rmm-lib-smc
)

target_link_libraries(rmm-lib-attestation
  PUBLIC
    rmm-lib-allocator
    rmm-lib-measurement
    rmm-mbedtls
    t_cose)

target_include_directories(rmm-lib-attestation
    PUBLIC "include"
    PRIVATE "src")

target_sources(rmm-lib-attestation
    PRIVATE
        "src/attestation_key.c"
        "src/attestation_rnd.c"
        "src/attestation_token.c"
        "src/attestation_utils.c")

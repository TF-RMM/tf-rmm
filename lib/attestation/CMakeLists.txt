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

arm_config_option(
    NAME ATTEST_PLAT_TOKEN_SIZE
    HELP "Maximum size in bytes expected for the Attestation platform token"
    TYPE STRING
    DEFAULT 0x1000
    ADVANCED)

target_compile_definitions(rmm-lib-attestation
    PRIVATE "MBEDTLS_ECP_MAX_OPS=${MBEDTLS_ECP_MAX_OPS}U")

target_compile_definitions(rmm-lib-attestation
    PRIVATE "ATTEST_PLAT_TOKEN_SIZE=U(${ATTEST_PLAT_TOKEN_SIZE})")

MATH(EXPR CCA_TOKEN_BUFFER_BYTES "${RMM_CCA_TOKEN_BUFFER} * 0x1000")
if (${CCA_TOKEN_BUFFER_BYTES} LESS ${ATTEST_PLAT_TOKEN_SIZE})
    message(FATAL_ERROR "RMM_CCA_TOKEN_BUFFER size is less than ATTEST_PLAT_TOKEN_SIZE")
endif()

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

if(HOST_VARIANT STREQUAL "host_cbmc")
    target_sources(rmm-lib-attestation
       PRIVATE "src/fake_host/cbmc_attestation.c")
    # In case of 'host_cbmc' variant no further source files are added to
    # the build.
    return()
endif()

target_sources(rmm-lib-attestation
    PRIVATE
        "src/attestation_key.c"
        "src/attestation_rnd.c"
        "src/attestation_token.c"
        "src/attestation_utils.c")

if (ATTEST_EL3_TOKEN_SIGN)
    target_sources(rmm-lib-attestation
        PRIVATE
        "src/attestation_el3_token_sign.c")
endif()

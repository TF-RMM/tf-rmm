#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# The attestation app is not included in the CBMC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    add_library(rmm-app-attestation-elf INTERFACE)
    return()
endif()

add_subdirectory("mbedtls_attest")
add_subdirectory("qcbor")
add_subdirectory("t_cose")

include("${CMAKE_CURRENT_SOURCE_DIR}/../../common/el0_app/CommonApp.cmake")

set(ATTESTATION_APP_ID 211)

arm_config_option(
    NAME ATTESTATION_APP_STACK_SIZE
    HELP "Number of pages to use for the Attestation app stack"
    TYPE STRING
    DEFAULT 2
    ADVANCED)

arm_config_option(
    NAME ATTESTATION_APP_HEAP_SIZE
    HELP "Number of pages to use for the Attestation app heap"
    TYPE STRING
    DEFAULT 3
    ADVANCED)

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

MATH(EXPR CCA_TOKEN_BUFFER_BYTES "${RMM_CCA_TOKEN_BUFFER} * 0x1000")
if (${CCA_TOKEN_BUFFER_BYTES} LESS ${ATTEST_PLAT_TOKEN_SIZE})
    message(FATAL_ERROR "RMM_CCA_TOKEN_BUFFER size is less than ATTEST_PLAT_TOKEN_SIZE")
endif()

add_el0_app(
    APP_NAME attestation
    APP_ID ${ATTESTATION_APP_ID}
    APP_DISPLAY_NAME "attestation_app"
    STACK_SIZE_VAR ATTESTATION_APP_STACK_SIZE
    HEAP_SIZE_VAR ATTESTATION_APP_HEAP_SIZE
    SOURCES
        "src/attest_app.c"
        "src/attest_measurement.c"
        "src/attestation_key.c"
        "src/attestation_token.c"
        "src/attestation_utils.c"
    LINK_LIBRARIES
        qcbor
        rmm-lib-arch
        rmm-lib-common
        rmm-lib-console
        rmm-lib-debug
        rmm-lib-libc
        rmm-lib-smc
        rmm-lib-xlat
        t_cose
)

# Add attestation-specific compile definitions
target_compile_definitions(rmm-app-attestation-elf
    PRIVATE
        "ATTEST_PLAT_TOKEN_SIZE=U(${ATTEST_PLAT_TOKEN_SIZE})"
        "MBEDTLS_ECP_MAX_OPS=${MBEDTLS_ECP_MAX_OPS}U"
)

# Add fake_host specific sources
if(RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-app-attestation-elf
        PRIVATE "src/fake_host/attest_app_host.c")
endif()

# Propagate EL0_APP_BIN_LIST to parent scope
set(EL0_APP_BIN_LIST ${EL0_APP_BIN_LIST} PARENT_SCOPE)

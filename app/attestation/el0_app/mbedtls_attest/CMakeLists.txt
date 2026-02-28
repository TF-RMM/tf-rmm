#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

include(${CMAKE_SOURCE_DIR}/cmake/Sanitizers.cmake)

set (MBEDTLS_TARGET_PREFIX "attest_")

# The Mbed TLS library is not included in the CBMC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    add_library(rmm-app-attestation-mbedtls INTERFACE)
    return()
endif()

set(MBEDTLS_SRC_DIR "${RMM_SOURCE_DIR}/ext/mbedtls")
set(MBEDTLS_BIN_DIR "${CMAKE_CURRENT_BINARY_DIR}/mbedtls_attest")

# Starting Mbed TLS 3.x release, mbedtls/library/CMakeLists.txt has dependency on
# link_to_source() function that is in mbedtls/CMakeLists.txt, so define a dummy
# link_to_source here.
function(link_to_source base_name)
endfunction(link_to_source)

# Ensure that the CFlags modifications are local in scope and only apply to
# MbedTLS build
if(RMM_FPU_USE_AT_REL2)
    set(BACKUP_C_FLAGS "${CMAKE_C_FLAGS}")
    # Enable using floating point registers for mbed TLS
    string(REPLACE "-mgeneral-regs-only" "" CMAKE_C_FLAGS ${CMAKE_C_FLAGS})
    # Enable using crypto and sha instructions
    string(REGEX REPLACE "(march=[^\\ ]*)" "\\1+sha3+crypto+nosve" CMAKE_C_FLAGS
        ${CMAKE_C_FLAGS})
    strip_sanitizer_flags()
    add_subdirectory("${MBEDTLS_SRC_DIR}/library" "${MBEDTLS_BIN_DIR}/library"
        EXCLUDE_FROM_ALL)

    set(CMAKE_C_FLAGS "${BACKUP_C_FLAGS}")
else()
    set(BACKUP_C_FLAGS "${CMAKE_C_FLAGS}")
    strip_sanitizer_flags()
    add_subdirectory("${MBEDTLS_SRC_DIR}/library" "${MBEDTLS_BIN_DIR}/library"
        EXCLUDE_FROM_ALL)
    set(CMAKE_C_FLAGS "${BACKUP_C_FLAGS}")
endif()

add_library(rmm-app-attestation-mbedtls INTERFACE)

# Patching is done by the original mbedTLS build. So make sure that this
# library depends on the original one.
add_dependencies(rmm-app-attestation-mbedtls rmm-mbedtls)

target_include_directories(rmm-app-attestation-mbedtls INTERFACE
    "${RMM_SOURCE_DIR}/app/attestation/el0_app/mbedtls_attest"
    "${MBEDTLS_SRC_DIR}/include")
target_compile_definitions(rmm-app-attestation-mbedtls INTERFACE
    "-DMBEDTLS_CONFIG_FILE=<rmm_mbedtls_config_attest.h>")

# Include targets mbedcrypto
set(MBEDTLS_LIBS mbedcrypto)

foreach(MBEDTLS_LIB IN ITEMS ${MBEDTLS_LIBS})
    target_include_directories(${MBEDTLS_TARGET_PREFIX}${MBEDTLS_LIB} PUBLIC
        "${RMM_SOURCE_DIR}/app/attestation/el0_app/mbedtls_attest"
        "${MBEDTLS_SRC_DIR}/include")
    target_compile_definitions(${MBEDTLS_TARGET_PREFIX}${MBEDTLS_LIB} PUBLIC
        "-DMBEDTLS_CONFIG_FILE=<rmm_mbedtls_config_attest.h>")
    target_link_libraries(rmm-app-attestation-mbedtls INTERFACE ${MBEDTLS_TARGET_PREFIX}${MBEDTLS_LIB})
    target_link_libraries(${MBEDTLS_TARGET_PREFIX}${MBEDTLS_LIB} PRIVATE rmm-app-common-el0_app)
endforeach()

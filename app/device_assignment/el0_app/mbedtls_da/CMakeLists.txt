#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

set (MBEDTLS_TARGET_PREFIX "da_")

# The Mbed TLS library is not included in the CBMC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    add_library(rmm-app-da-mbedtls INTERFACE)
    return()
endif()

set(MBEDTLS_SRC_DIR "${RMM_SOURCE_DIR}/ext/mbedtls")
set(MBEDTLS_BIN_DIR "${CMAKE_CURRENT_BINARY_DIR}/mbedtls_da")

# Starting Mbed TLS 3.x release, mbedtls/library/CMakeLists.txt has dependency on
# link_to_source() function that is in mbedtls/CMakeLists.txt, so define a dummy
# link_to_source here.
function(link_to_source base_name)
endfunction(link_to_source)

add_subdirectory("${MBEDTLS_SRC_DIR}/library" "${MBEDTLS_BIN_DIR}/library"
                    EXCLUDE_FROM_ALL)

add_library(rmm-app-da-mbedtls INTERFACE)

# Patching is done by the original mbedTLS build. So make sure that this
# library depends on the original one.
add_dependencies(rmm-app-da-mbedtls rmm-mbedtls)

target_include_directories(rmm-app-da-mbedtls INTERFACE
    "${RMM_SOURCE_DIR}/app/device_assignment/el0_app/mbedtls_da"
    "${MBEDTLS_SRC_DIR}/include")
target_compile_definitions(rmm-app-da-mbedtls INTERFACE
    "-DMBEDTLS_CONFIG_FILE=<rmm_mbedtls_config_da.h>")

# Include targets mbedcrypto and mbedx509
set(MBEDTLS_LIBS mbedcrypto)
list(APPEND MBEDTLS_LIBS mbedx509)

foreach(MBEDTLS_LIB IN ITEMS ${MBEDTLS_LIBS})
    target_include_directories(${MBEDTLS_TARGET_PREFIX}${MBEDTLS_LIB} PUBLIC
        "${RMM_SOURCE_DIR}/app/device_assignment/el0_app/mbedtls_da"
        "${MBEDTLS_SRC_DIR}/include")
    target_compile_definitions(${MBEDTLS_TARGET_PREFIX}${MBEDTLS_LIB} PUBLIC
        "-DMBEDTLS_CONFIG_FILE=<rmm_mbedtls_config_da.h>")
    target_link_libraries(rmm-app-da-mbedtls INTERFACE ${MBEDTLS_TARGET_PREFIX}${MBEDTLS_LIB})
    target_link_libraries(${MBEDTLS_TARGET_PREFIX}${MBEDTLS_LIB} PRIVATE rmm-app-common-el0_app)
endforeach()

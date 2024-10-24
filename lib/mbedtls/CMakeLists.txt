#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# The Mbed TLS library is not included in the CBMC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    add_library(rmm-mbedtls INTERFACE)
    return()
endif()

set(MBEDTLS_SRC_DIR "${RMM_SOURCE_DIR}/ext/mbedtls")
set(MBEDTLS_BIN_DIR "${CMAKE_BINARY_DIR}/ext/mbedtls")

# Patch Mbed TLS before add_subdirectory() this allows to patch CMake files.
# For details see commit messages in patch files.
set(MBEDTLS_PATCH_DIR "${RMM_SOURCE_DIR}/configs/mbedtls")
set(MBEDTLS_PATCH_FILES
    "${MBEDTLS_PATCH_DIR}/0001-Remove-compiler-options-for-clang.patch"
    "${MBEDTLS_PATCH_DIR}/0002-Disable-explicit_bzero.patch")

Git_Apply_Patches(${MBEDTLS_SRC_DIR} "${MBEDTLS_PATCH_FILES}")

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

    add_subdirectory("${MBEDTLS_SRC_DIR}/library" "${MBEDTLS_BIN_DIR}/library"
        EXCLUDE_FROM_ALL)

    set(CMAKE_C_FLAGS "${BACKUP_C_FLAGS}")
else()
    add_subdirectory("${MBEDTLS_SRC_DIR}/library" "${MBEDTLS_BIN_DIR}/library"
        EXCLUDE_FROM_ALL)
endif()

add_library(rmm-mbedtls INTERFACE)
target_include_directories(rmm-mbedtls INTERFACE
    "${RMM_SOURCE_DIR}/configs/mbedtls"
    "${MBEDTLS_SRC_DIR}/include")
target_compile_definitions(rmm-mbedtls INTERFACE
    "-DMBEDTLS_CONFIG_FILE=<rmm_mbedtls_config.h>")

# Include targets mbedcrypto, mbedx509
set(MBEDTLS_LIBS mbedcrypto)
if(RMM_V1_1)
    list(APPEND MBEDTLS_LIBS mbedx509)
endif()

foreach(MBEDTLS_LIB IN ITEMS ${MBEDTLS_LIBS})
    target_include_directories(${MBEDTLS_LIB} PUBLIC
        "${RMM_SOURCE_DIR}/configs/mbedtls"
        "${MBEDTLS_SRC_DIR}/include")
    target_compile_definitions(${MBEDTLS_LIB} PUBLIC
        "-DMBEDTLS_CONFIG_FILE=<rmm_mbedtls_config.h>")
    target_link_libraries(rmm-mbedtls INTERFACE ${MBEDTLS_LIB})
endforeach()

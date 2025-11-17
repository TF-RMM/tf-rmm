#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# This compiles libraries in ext/libspdm project to add SPDM requester protocol
# support in RMM.
#
add_library(rmm-spdm_requester INTERFACE)

# Skip rmm-spdm_requester from CMBC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    return()
endif()

# Set LIBSPDM_DIR. Note: This variable is used by libspdm CMake.
# libspdm is fetched to ext/libspdm in RMM source.
set(LIBSPDM_DIR "${RMM_SOURCE_DIR}/ext/libspdm")
set(LIBSPDM_BIN_DIR "${CMAKE_BINARY_DIR}/ext/libspdm")
set(MBEDTLS_SRC_DIR "${RMM_SOURCE_DIR}/ext/mbedtls")


# Apply RMM specific patches to libspdm once cloned.
set(LIBSPDM_PATCH_DIR "${RMM_SOURCE_DIR}/configs/libspdm")
set(LIBSPDM_PATCH_FILES
    "${LIBSPDM_PATCH_DIR}/0001-cryptlib_mbedtls-use-external-Mbed-TLS.patch"
    "${LIBSPDM_PATCH_DIR}/0002-fix-libspdm_hmac_new-return-and-LIBSPDM_STATUS_CONST.patch"
    "${LIBSPDM_PATCH_DIR}/0003-get_certificate-do-not-store-cert_chain-content.patch"
    "${LIBSPDM_PATCH_DIR}/0004-add-LIBSPDM_DATA_PEER_USED_CERT_CHAIN_PUBLIC_KEY.patch"
    "${LIBSPDM_PATCH_DIR}/0005-get_measurements-do-not-store-measurement-record.patch"
    "${LIBSPDM_PATCH_DIR}/0006-fix-undefined-behavior-for-left-shift.patch"
    )
Git_Apply_Patches(${LIBSPDM_DIR} "${LIBSPDM_PATCH_FILES}")

# Set libspdm config file
set(LIBSPDM_CONFIG "LIBSPDM_CONFIG=<rmm_libspdm_config.h>")

# Below are the list of core SPDM libraries required for requester side protocol.
set(SOURCE_DIRS
    ${LIBSPDM_DIR}/library/spdm_common_lib
    ${LIBSPDM_DIR}/library/spdm_crypt_lib
    ${LIBSPDM_DIR}/library/spdm_requester_lib
    ${LIBSPDM_DIR}/library/spdm_secured_message_lib)

#
# Below are the list of os_stub libraries in libspdm that LIBSPDM_CORE_LIBS
# depends on.
# TODO: memlib and debuglib should be reimplemented for aarch64.
#
set(SOURCE_DIRS
    ${SOURCE_DIRS}
    ${LIBSPDM_DIR}/os_stub/cryptlib_mbedtls
    ${LIBSPDM_DIR}/os_stub/memlib
    ${LIBSPDM_DIR}/os_stub/debuglib)

# For aarch64 build include aarch64_stub libraries that provides
# libspdm_get_random_number_64, libspdm_sleep else include libspdm's os_stub
# libraries.
if(RMM_ARCH STREQUAL aarch64)
    set(SOURCE_DIRS
        ${SOURCE_DIRS}
        ${CMAKE_CURRENT_SOURCE_DIR}/aarch64_stub/spdm_malloclib
        ${CMAKE_CURRENT_SOURCE_DIR}/aarch64_stub/spdm_rnglib
        ${CMAKE_CURRENT_SOURCE_DIR}/aarch64_stub/spdm_timelib)
else()
    set(SOURCE_DIRS
        ${SOURCE_DIRS}
        ${LIBSPDM_DIR}/os_stub/malloclib
        ${LIBSPDM_DIR}/os_stub/rnglib
        ${LIBSPDM_DIR}/os_stub/platform_lib)
endif()

# Disable -Wstrict-overflow for libspdm
set(BACKUP_C_FLAGS "${CMAKE_C_FLAGS}")
string(REPLACE "-Wstrict-overflow" "" CMAKE_C_FLAGS ${CMAKE_C_FLAGS})

# Add all source directories
foreach(SOURCE_DIR IN LISTS SOURCE_DIRS)
    # Get the library basename
    get_filename_component(SPDM_LIB "${SOURCE_DIR}" NAME)

    # Add the source directory
    add_subdirectory(${SOURCE_DIR} ${LIBSPDM_BIN_DIR}/${SPDM_LIB})

    target_include_directories(${SPDM_LIB} PRIVATE
        "${RMM_SOURCE_DIR}/app/device_assignment/el0_app/spdm_requester"
        "${RMM_SOURCE_DIR}/app/device_assignment/el0_app/mbedtls_da"
        "${MBEDTLS_SRC_DIR}/include")
    target_compile_definitions(${SPDM_LIB} PRIVATE
        ${LIBSPDM_CONFIG}
        "-DMBEDTLS_CONFIG_FILE=<rmm_mbedtls_config_da.h>")

    # RMM default compile flags are passed to libspdm. Disable few warnings
    # reported as error until libspdm resolves these issues.
    target_compile_options(${SPDM_LIB} PRIVATE
        "-Wno-incompatible-pointer-types"
        "-Wno-unused-parameter"
        "-Wno-old-style-declaration"
        "-Wno-sign-compare")

    target_link_libraries(rmm-spdm_requester INTERFACE ${SPDM_LIB})
endforeach()

set(CMAKE_C_FLAGS "${BACKUP_C_FLAGS}")

# Set includes and compile definitions for this interface library
target_include_directories(rmm-spdm_requester INTERFACE
    "${RMM_SOURCE_DIR}/configs/libspdm"
    "${LIBSPDM_DIR}/include")
target_compile_definitions(rmm-spdm_requester INTERFACE
    ${LIBSPDM_CONFIG})

# Manually create internal dependencies for libspdm libraries
target_link_libraries(spdm_requester_lib PRIVATE spdm_common_lib spdm_crypt_lib)
target_link_libraries(spdm_secured_message_lib PRIVATE spdm_crypt_lib)
target_link_libraries(spdm_common_lib PRIVATE spdm_crypt_lib)

# Manually create external dependencies for libspdm libraries
target_link_libraries(cryptlib_mbedtls PRIVATE rmm-app-da-mbedtls)

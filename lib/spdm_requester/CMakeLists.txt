#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/tools/common")
include(GitUtils)
include(FetchContent)

# Skip rmm-lib-spdm_requester from CMBC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    add_library(rmm-lib-spdm_requester INTERFACE)
    return()
endif()

#
# Git clone libspdm. We manually clone instead of adding this as a submodule
# because adding libspdm as a submodule causes recursive clone to fetch all
# dependency projects by libspdm.
#
# LIBSPDM_SHA points to v3.3.0 + mbedtls 3.6.0
#
set(LIBSPDM_URL "https://github.com/DMTF/libspdm.git")
set(LIBSPDM_SHA "e5eb4484705fb3fb5cd25e773477c456096bd837")
set(LIBSPDM_SRC "${RMM_SOURCE_DIR}/ext/libspdm")

FetchContent_Declare(libspdm
    GIT_REPOSITORY	${LIBSPDM_URL}
    GIT_TAG		${LIBSPDM_SHA}
    SOURCE_DIR		${LIBSPDM_SRC}
    GIT_SUBMODULES	""
    GIT_PROGRESS	1)

FetchContent_GetProperties(libspdm)
if(NOT libspdm_POPULATED)
    message("Fetching: ${LIBSPDM_URL} SHA: ${LIBSPDM_SHA}")
    FetchContent_Populate(libspdm)
    message("libspdm SRC: ${LIBSPDM_SRC}")
endif()

# Set LIBSPDM_DIR. Note: This variable is used by libspdm CMake.
# libspdm is fetched to ext/libspdm in RMM source.
set(LIBSPDM_DIR ${LIBSPDM_SRC})
set(LIBSPDM_BIN_DIR "${CMAKE_BINARY_DIR}/ext/libspdm")
set(MBEDTLS_SRC_DIR "${RMM_SOURCE_DIR}/ext/mbedtls")

# Apply RMM specific patches to libspdm once cloned.
set(LIBSPDM_PATCH_DIR "${RMM_SOURCE_DIR}/configs/libspdm")
set(LIBSPDM_PATCH_FILES
    "${LIBSPDM_PATCH_DIR}/0001-cryptlib_mbedtls-use-external-Mbed-TLS.patch"
    )
Git_Apply_Patches(${LIBSPDM_DIR} "${LIBSPDM_PATCH_FILES}")

#
# This compiles libraries in ext/libspdm project to add SPDM requester protocol
# support in RMM.
#
add_library(rmm-lib-spdm_requester INTERFACE)

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
#
set(SOURCE_DIRS
    ${SOURCE_DIRS}
    ${LIBSPDM_DIR}/os_stub/cryptlib_mbedtls
    ${LIBSPDM_DIR}/os_stub/memlib)

# Add all source directories
foreach(SOURCE_DIR IN LISTS SOURCE_DIRS)
    # Get the library basename
    get_filename_component(SPDM_LIB "${SOURCE_DIR}" NAME)

    # Add the source directory
    add_subdirectory(${SOURCE_DIR} ${LIBSPDM_BIN_DIR}/${SPDM_LIB})

    target_include_directories(${SPDM_LIB} PRIVATE
        "${RMM_SOURCE_DIR}/configs/libspdm"
        "${RMM_SOURCE_DIR}/configs/mbedtls"
        "${MBEDTLS_SRC_DIR}/include")
    target_compile_definitions(${SPDM_LIB} PRIVATE
        ${LIBSPDM_CONFIG}
        "-DMBEDTLS_CONFIG_FILE=<rmm_mbedtls_config.h>")
    target_compile_options(${SPDM_LIB} PRIVATE
        "-Wno-incompatible-pointer-types")

    target_link_libraries(rmm-lib-spdm_requester INTERFACE ${SPDM_LIB})
endforeach()

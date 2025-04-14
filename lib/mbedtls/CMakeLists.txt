#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-mbedtls INTERFACE)

# The Mbed TLS library is not included in the CBMC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    return()
endif()

set(MBEDTLS_SRC_DIR "${RMM_SOURCE_DIR}/ext/mbedtls")

# Patch Mbed TLS before add_subdirectory() this allows to patch CMake files.
# For details see commit messages in patch files.
set(MBEDTLS_PATCH_DIR "${RMM_SOURCE_DIR}/configs/mbedtls")
set(MBEDTLS_PATCH_FILES
    "${MBEDTLS_PATCH_DIR}/0001-Remove-compiler-options-for-clang.patch"
    "${MBEDTLS_PATCH_DIR}/0002-Disable-explicit_bzero.patch"
    "${MBEDTLS_PATCH_DIR}/0003-refactor-alloc-Use-the-heap-structure-provided-by-ap.patch")

Git_Apply_Patches(${MBEDTLS_SRC_DIR} "${MBEDTLS_PATCH_FILES}")

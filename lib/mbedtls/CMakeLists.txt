#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

find_package(Python3 COMPONENTS Interpreter REQUIRED)
find_package(Git)

# The Mbed TLS library is not included in the CBMC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    add_library(rmm-mbedtls INTERFACE)
    return()
endif()

add_library(rmm-mbedtls INTERFACE)

set(MBEDTLS_SRC_DIR "${RMM_SOURCE_DIR}/ext/mbedtls")

target_include_directories(rmm-mbedtls INTERFACE ${RMM_SOURCE_DIR}/configs/mbedtls)
target_compile_definitions(rmm-mbedtls INTERFACE MBEDTLS_CONFIG_FILE=<mbedtls_config.h>)

include_directories(${RMM_SOURCE_DIR}/configs/mbedtls)
add_compile_definitions(MBEDTLS_CONFIG_FILE=<mbedtls_config.h>)

#
# Workaround for CMake not detecting size of pointer on AArch64 toolchain and
# causing MbedTLS compilation to print warning during configuration.
#
if(RMM_ARCH STREQUAL aarch64)
    set(CMAKE_SIZEOF_VOID_P 8)
endif()

set(ENABLE_PROGRAMS OFF CACHE BOOL "Setting for mbedtls program")
set(ENABLE_TESTING OFF CACHE BOOL "Setting for mbedtls tests")

# Ensure that the CFlags modifications are local in scope and only apply to
# MbedTLS build
set(BACKUP_C_CLAGS "${CMAKE_C_FLAGS}")

if(RMM_FPU_USE_AT_REL2)
    # Enable using floating point registers for mbed TLS
    string(REPLACE "-mgeneral-regs-only" "" CMAKE_C_FLAGS ${CMAKE_C_FLAGS})
    # Enable using crypto and sha instructions
    string(REGEX REPLACE "(march=[^\\ ]*)" "\\1+sha3+crypto" CMAKE_C_FLAGS ${CMAKE_C_FLAGS})
    # Enable using SHA256 and SHA512 instructions in MbedTLS
    string(APPEND CMAKE_C_FLAGS
            " -DMBEDTLS_SHA256_USE_A64_CRYPTO_ONLY=1 "
            " -DMBEDTLS_SHA512_USE_A64_CRYPTO_ONLY=1 ")
endif()

# Patch Mbed TLS if it is not patched yet.
# For details see commit messages in patch files.
set(MBEDTLS_PATCH_DIR "${RMM_SOURCE_DIR}/configs/mbedtls")
set(MBEDTLS_PATCH_FILES
    "${MBEDTLS_PATCH_DIR}/0001-Remove-compiler-options-for-clang.patch"
    "${MBEDTLS_PATCH_DIR}/0002-Disable-explicit_bzero.patch"
)

if(NOT EXISTS ${MBEDTLS_SRC_DIR}/.git)
    message(FATAL_ERROR "MbedTLS submodule not found")
endif()

set(REVERT_COMMAND "${GIT_EXECUTABLE}" checkout .)
execute_process(COMMAND ${REVERT_COMMAND}
    WORKING_DIRECTORY ${MBEDTLS_SRC_DIR}
)

foreach (MBEDTLS_PATCH_FILE ${MBEDTLS_PATCH_FILES})
    set(EXECUTE_COMMAND "${GIT_EXECUTABLE}" apply --verbose ${MBEDTLS_PATCH_FILE})
    execute_process(COMMAND ${EXECUTE_COMMAND}
        WORKING_DIRECTORY ${MBEDTLS_SRC_DIR}
        RESULT_VARIABLE PATCH_STATUS
        COMMAND_ECHO STDOUT
    )
    if (NOT PATCH_STATUS EQUAL 0)
        message( FATAL_ERROR "Failed to apply patches at ${WORKING_DIRECTORY}" )
    endif()
endforeach()

#
# Add the mbedtls subdirectory and exclude all targets in mbedtls from
# default `all` target
#
add_subdirectory("${MBEDTLS_SRC_DIR}" "${CMAKE_BINARY_DIR}/ext/mbedtls" EXCLUDE_FROM_ALL)

target_link_libraries(rmm-mbedtls INTERFACE mbedtls)

# Restore the original CXX flags.
set(CMAKE_C_FLAGS "${BACKUP_C_FLAGS}")

#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

find_package(Python3 COMPONENTS Interpreter REQUIRED)

add_library(rmm-mbedtls INTERFACE)
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

# The CFlags modifications are local in scope and only apply to MbedTLS build
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

#
# Add the mbedtls subdirectory and exclude all targets in mbedtls from
# default `all` target
#
add_subdirectory("${RMM_SOURCE_DIR}/ext/mbedtls" "${CMAKE_BINARY_DIR}/ext/medtls" EXCLUDE_FROM_ALL)

target_link_libraries(rmm-mbedtls INTERFACE mbedtls)

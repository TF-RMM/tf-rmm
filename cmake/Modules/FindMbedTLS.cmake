#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#[=======================================================================[.rst:
FindMbedTLS
===========

TODO: documentation.
#]=======================================================================]

include(FindPackageHandleStandardArgs)

find_path(MbedTLS_INCLUDE_DIR
    NAMES "mbedtls/build_info.h")

if(MbedTLS_INCLUDE_DIR)
    mark_as_advanced(MbedTLS_INCLUDE_DIR)

    set(MbedTLS_FOUND TRUE)
endif()

find_library(MbedTLS_Crypto_LIBRARY "mbedcrypto" PATHS "library" "lib")
find_library(MbedTLS_TLS_LIBRARY "mbedtls" PATHS "library" "lib")
find_library(MbedTLS_X509_LIBRARY "mbedx509" PATHS "library" "lib")

foreach(component IN ITEMS Crypto TLS X509)
    if(MbedTLS_${component}_LIBRARY)
        mark_as_advanced(MbedTLS_${component}_LIBRARY)

        set(MbedTLS_${component}_FOUND TRUE)
    endif()
endforeach()

find_package_handle_standard_args(MbedTLS HANDLE_COMPONENTS
    REQUIRED_VARS MbedTLS_FOUND MbedTLS_INCLUDE_DIR)

if(MbedTLS_FOUND)
    add_library(MbedTLS INTERFACE)

    target_include_directories(MbedTLS
        INTERFACE "${MbedTLS_INCLUDE_DIR}"
                  "${RMM_SOURCE_DIR}/configs/mbedtls")

    target_compile_definitions(MbedTLS
        INTERFACE "MBEDTLS_CONFIG_FILE=<mbedtls_config.h>")

    foreach(component IN ITEMS Crypto TLS X509)
        if(MbedTLS_${component}_LIBRARY)
            add_library(MbedTLS::${component} UNKNOWN IMPORTED)

            set_target_properties(MbedTLS::${component}
                PROPERTIES IMPORTED_LOCATION "${MbedTLS_${component}_LIBRARY}")

            target_link_libraries(MbedTLS::${component}
                INTERFACE MbedTLS)
        endif()
    endforeach()
endif()

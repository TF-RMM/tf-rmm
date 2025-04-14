#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(spdm_rnglib)

target_sources(spdm_rnglib
    PRIVATE "spdm_rnglib.c")

target_link_libraries(spdm_rnglib PRIVATE rmm-app-da-mbedtls)

target_include_directories(spdm_rnglib PRIVATE
    ${LIBSPDM_DIR}/include
    ${LIBSPDM_DIR}/include/hal
    ${LIBSPDM_DIR}/os_stub/include)

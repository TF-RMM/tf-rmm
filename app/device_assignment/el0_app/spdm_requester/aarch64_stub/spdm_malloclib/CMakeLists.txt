#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(spdm_malloclib)

target_sources(spdm_malloclib
    PRIVATE "spdm_malloclib.c")

target_include_directories(spdm_malloclib PRIVATE
    ${LIBSPDM_DIR}/include
    ${LIBSPDM_DIR}/include/hal
    ${LIBSPDM_DIR}/os_stub/include)

target_link_libraries(spdm_malloclib PRIVATE da-rmm-mbedtls)

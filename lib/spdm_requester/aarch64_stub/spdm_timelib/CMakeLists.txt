#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#
add_library(spdm_timelib)

target_sources(spdm_timelib
    PRIVATE "spdm_time.c")

target_include_directories(spdm_timelib PRIVATE
    ${LIBSPDM_DIR}/include
    ${LIBSPDM_DIR}/include/hal
    ${LIBSPDM_DIR}/os_stub/include)

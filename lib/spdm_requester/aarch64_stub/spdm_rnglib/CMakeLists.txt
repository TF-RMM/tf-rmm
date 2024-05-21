#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

set(src_spdm_rnglib
    spdm_rnglib.c)

add_library(spdm_rnglib STATIC ${src_spdm_rnglib})
target_include_directories(spdm_rnglib PRIVATE
    ${LIBSPDM_DIR}/include
    ${LIBSPDM_DIR}/include/hal
    ${LIBSPDM_DIR}/os_stub/include)

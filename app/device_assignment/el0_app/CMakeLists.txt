#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# TODO: The C file generating logic is general for all the apps.
# need to move it to a common location somehow.

# The random app is not included in the CBMC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    return()
endif()

add_subdirectory("mbedtls_da")
add_subdirectory("spdm_requester")

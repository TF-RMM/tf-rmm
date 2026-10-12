#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# Compile the Host DA helpers into each variant that uses them.
add_library(rmm-host-da INTERFACE)

target_sources(rmm-host-da
    INTERFACE "${CMAKE_CURRENT_SOURCE_DIR}/src/host_da.c"
              "${CMAKE_CURRENT_SOURCE_DIR}/src/host_sro.c"
              "${CMAKE_CURRENT_SOURCE_DIR}/src/host_da_crypto_utils.c")

target_include_directories(rmm-host-da
    INTERFACE "${CMAKE_CURRENT_SOURCE_DIR}/include")

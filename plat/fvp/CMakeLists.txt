#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-fvp)

add_subdirectory("${RMM_SOURCE_DIR}/drivers/pl011" ${RMM_BINARY_DIR}/drivers/pl011)
add_subdirectory("${RMM_SOURCE_DIR}/plat/common" ${RMM_BINARY_DIR}/plat/common)

target_link_libraries(rmm-fvp
    PRIVATE rmm-driver-pl011
            rmm-lib
            rmm-plat-common)

target_sources(rmm-fvp
    PRIVATE "src/fvp_setup.c"
            "src/fvp_granule.c"
            "src/fvp_memory.c")

target_include_directories(rmm-fvp
    PRIVATE "src/include")

add_library(rmm-platform ALIAS rmm-fvp)

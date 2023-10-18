#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-qemu)

add_subdirectory("${RMM_SOURCE_DIR}/drivers/pl011" ${RMM_BINARY_DIR}/drivers/pl011)
add_subdirectory("${RMM_SOURCE_DIR}/plat/common" ${RMM_BINARY_DIR}/plat/common)

target_link_libraries(rmm-qemu
    PRIVATE rmm-driver-pl011
            rmm-lib
            rmm-plat-common)

target_sources(rmm-qemu
    PRIVATE "src/qemu_setup.c"
            "src/qemu_granule.c"
            "src/qemu_memory.c")

target_include_directories(rmm-qemu
    PRIVATE "src/include")

add_library(rmm-platform ALIAS rmm-qemu)

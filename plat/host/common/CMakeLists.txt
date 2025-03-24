#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

arm_config_option(
    NAME HOST_DRAM_SIZE
    HELP "Host memory size that will be used as physical DRAM"
    TYPE STRING
    DEFAULT "0x20000000")

arm_config_option(
    NAME HOST_NCOH_DEV_SIZE
    HELP "Host memory size that will be used as non-coherent device granules"
    TYPE STRING
    DEFAULT "0xA000")

add_library(rmm-host-common)

target_link_libraries(rmm-host-common
    PRIVATE rmm-lib
            rmm-plat-common)

target_link_libraries(rmm-host-common
    PUBLIC  rmm-host-support)

add_subdirectory("mbedtls_host")

target_link_libraries(rmm-host-common
    PRIVATE  rmm-host-mbedtls) # Mbed TLS is added for host emulating signing in EL3

target_sources(rmm-host-common
    PRIVATE "src/host_console.c"
            "src/host_harness_cmn.c"
            "src/host_platform_api_cmn.c"
            "src/host_rmi_wrappers.c"
            "src/host_utils.c")

target_include_directories(rmm-host-common
    PUBLIC "include"
    PRIVATE "src")

target_compile_definitions(rmm-host-common
    PUBLIC "HOST_DRAM_SIZE=UL(${HOST_DRAM_SIZE})")

target_compile_definitions(rmm-host-common
    PUBLIC "HOST_NCOH_DEV_SIZE=UL(${HOST_NCOH_DEV_SIZE})")

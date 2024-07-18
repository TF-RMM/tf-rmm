#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

arm_config_option(
    NAME HOST_MEM_SIZE
    HELP "Host memory size that will be used as physical granules"
    DEFAULT "0x40000000")

add_library(rmm-host-common)

target_link_libraries(rmm-host-common
    PRIVATE  rmm-lib
             rmm-plat-common)

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
    PUBLIC "HOST_MEM_SIZE=UL(${HOST_MEM_SIZE})")

#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-host-common)

target_link_libraries(rmm-host-common
    PRIVATE  rmm-lib
             rmm-plat-common)

target_sources(rmm-host-common
    PRIVATE "src/host_harness_cmn.c"
            "src/host_platform_api_cmn.c"
            "src/host_rmi_wrappers.c"
            "src/host_utils.c")

target_include_directories(rmm-host-common
    PUBLIC "include")

target_compile_definitions(rmm-host-common
    PUBLIC "HOST_MEM_SIZE=UL(${HOST_MEM_SIZE})")

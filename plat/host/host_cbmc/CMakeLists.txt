#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-plat-host_cbmc)

arm_config_option(
    NAME RMM_CBMC_STATIC_ANALYSIS
    HELP "Enable CBMC static analysis."
    DEFAULT TRUE FORCE)

target_link_libraries(rmm-plat-host_cbmc
    PRIVATE rmm-lib
    PUBLIC rmm-host-common)

target_sources(rmm-plat-host_cbmc
    PRIVATE
        "src/host_harness.c"
        "src/plat_init.c"
        "src/tb_common.c"
        "src/tb_granules.c"
        "src/tb_measurement.c"
        "src/tb_ns_access.c"
        "src/tb_realm.c"
        "src/tb_rec.c"
        "src/tb_rtt.c"
        "src/tb.c"
        )

target_include_directories(rmm-plat-host_cbmc
    PUBLIC "include")

add_library(rmm-platform ALIAS rmm-plat-host_cbmc)

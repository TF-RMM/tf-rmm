#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
# SPDX-FileCopyrightText: Copyright (c) 2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
#

add_library(rmm-lib-smmuv3)

#
# Driver option controlling debug messages:
#   "ON"  selects LOG_LEVEL_INFO.
#   "OFF" selects LOG_LEVEL_VERBOSE.
#
arm_config_option(
    NAME SMMU_LOG
    HELP "Enable SMMUv3 driver logging"
    TYPE BOOL
    DEFAULT "ON")

if(SMMU_LOG)
target_compile_definitions(rmm-lib-smmuv3
    PRIVATE "SMMU_LOG=1")
endif()

target_link_libraries(rmm-lib-smmuv3
    PRIVATE rmm-lib-arch
            rmm-lib-debug
            rmm-lib-mec
            rmm-lib-rmm_el3_ifc
            rmm-lib-s2tt
            rmm-lib-smc
            rmm-lib-xlat
            rmm-lib-xlat_low_va)

target_include_directories(rmm-lib-smmuv3
    PUBLIC "include"
    PRIVATE "src"
            "src/${RMM_ARCH}")

target_sources(rmm-lib-smmuv3
    PRIVATE "src/smmuv3_psmmu.c"
            "src/smmuv3.c"
            "src/smmuv3_tlbi.c")

include("tests/CMakeLists.txt")

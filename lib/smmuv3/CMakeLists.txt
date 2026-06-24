#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
# SPDX-FileCopyrightText: Copyright (c) 2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
#

add_library(rmm-lib-smmuv3)

#
# Maximum log2 size of the SMMU Command Queue (CMDQ).
#
# The default value of 8 allows up to 256 command entries,
# corresponding to a 4 KiB Command Queue (16 bytes per entry).
#
arm_config_option(
    NAME SMMU_MAX_LOG2_CMDQ_SIZE
    HELP "Maximum LOG2 size of CMDQ"
    TYPE STRING
    DEFAULT 8)

if(SMMU_MAX_LOG2_CMDQ_SIZE GREATER 19)
    message(FATAL_ERROR "SMMU_MAX_LOG2_CMDQ_SIZE cannot exceed 19")
endif()

target_compile_definitions(rmm-lib-smmuv3
    PRIVATE "SMMU_MAX_LOG2_CMDQ_SIZE=${SMMU_MAX_LOG2_CMDQ_SIZE}U")

#
# Maximum log2 size of the Event Queue (EVTQ).
#
# The default value of 7 allows up to 128 event records,
# corresponding to a 4 KiB Event Queue (32 bytes per record).
#
arm_config_option(
    NAME SMMU_MAX_LOG2_EVTQ_SIZE
    HELP "Maximum LOG2 size of EVTQ"
    TYPE STRING
    DEFAULT 7)

if(SMMU_MAX_LOG2_EVTQ_SIZE GREATER 19)
    message(FATAL_ERROR "SMMU_MAX_LOG2_EVTQ_SIZE cannot exceed 19")
endif()

target_compile_definitions(rmm-lib-smmuv3
    PRIVATE "SMMU_MAX_LOG2_EVTQ_SIZE=${SMMU_MAX_LOG2_EVTQ_SIZE}U")

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

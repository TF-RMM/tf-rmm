#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
# SPDX-FileCopyrightText: Copyright (c) 2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
#

add_library(rmm-lib-smmuv3)

#
# StreamID split point for multi-level table. To keep L2
# table size the same as GRANULE_SIZE, 6 is chosen as split point.
#
arm_config_option(
    NAME SMMU_STRTAB_SPLIT
    HELP "StreamID split point of a 2-level Stream table"
    TYPE STRING
    DEFAULT 6
    ADVANCED ON)

# Allowed values for SMMU_STRTAB_SPLIT
set(ALLOWED_SPLITS 6 8 10)

# Enforce that the value is one of 6, 8, or 10
if(NOT SMMU_STRTAB_SPLIT IN_LIST ALLOWED_SPLITS)
    string(JOIN "," ALLOWED_SPLITS_STR ${ALLOWED_SPLITS})
    message(FATAL_ERROR
        "Invalid value for SMMU_STRTAB_SPLIT: ${SMMU_STRTAB_SPLIT}\n"
        "Allowed values are: ${ALLOWED_SPLITS_STR}")
endif()

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

target_compile_definitions(rmm-lib-smmuv3
    PRIVATE "SMMU_STRTAB_SPLIT=${SMMU_STRTAB_SPLIT}U")

if(SMMU_LOG)
target_compile_definitions(rmm-lib-smmuv3
    PRIVATE "SMMU_LOG=1")
endif()

target_link_libraries(rmm-lib-smmuv3
    PRIVATE rmm-lib)

target_include_directories(rmm-lib-smmuv3
    PUBLIC "include"
    PRIVATE "src/${RMM_ARCH}")

target_sources(rmm-lib-smmuv3
    PRIVATE "src/${RMM_ARCH}/smmuv3.c"
            "src/${RMM_ARCH}/smmuv3_tlbi.c")

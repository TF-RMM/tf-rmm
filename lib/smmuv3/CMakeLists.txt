#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
# SPDX-FileCopyrightText: Copyright (c) 2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
#

add_library(rmm-lib-smmuv3)

#
# Maximum log2 size of CMDQ
#
arm_config_option(
    NAME SMMU_MAX_LOG2_CMDQ_SIZE
    HELP "Maximum LOG2 size of CMDQ"
    TYPE STRING
    DEFAULT 7)

if(SMMU_MAX_LOG2_CMDQ_SIZE GREATER 19)
    message(FATAL_ERROR "SMMU_MAX_LOG2_CMDQ_SIZE cannot exceed 19")
endif()

#
# Maximum log2 size of EVTQ
#
arm_config_option(
    NAME SMMU_MAX_LOG2_EVTQ_SIZE
    HELP "Maximum LOG2 size of EVTQ"
    TYPE STRING
    DEFAULT 7)

if(SMMU_MAX_LOG2_EVTQ_SIZE GREATER 19)
    message(FATAL_ERROR "SMMU_MAX_LOG2_EVTQ_SIZE cannot exceed 19")
endif()

#
# Maximum width of StreamID
#
arm_config_option(
    NAME SMMU_MAX_SID_BITS
    HELP "Maximum number of SMMU Stream ID bits allowed"
    TYPE STRING
    DEFAULT 16)

if(SMMU_MAX_SID_BITS GREATER 32)
    message(FATAL_ERROR "SMMU_MAX_SID_BITS cannot exceed 32")
endif()

#
# StreamID split point for multi-level table
#
arm_config_option(
    NAME SMMU_STRTAB_SPLIT
    HELP "StreamID split point of a 2-level Stream table"
    TYPE STRING
    DEFAULT 8)

# Allowed values for SMMU_STRTAB_SPLIT
set(ALLOWED_SPLITS 6 8 10)

# Enforce that the value is one of 6, 8, or 10
if(NOT SMMU_STRTAB_SPLIT IN_LIST ALLOWED_SPLITS)
    string(JOIN "," ALLOWED_SPLITS_STR ${ALLOWED_SPLITS})
    message(FATAL_ERROR
        "Invalid value for SMMU_STRTAB_SPLIT: ${SMMU_STRTAB_SPLIT}\n"
        "Allowed values are: ${ALLOWED_SPLITS_STR}")
endif()

if(SMMU_MAX_SID_BITS LESS SMMU_STRTAB_SPLIT)
    message(FATAL_ERROR
        "SMMU_STRTAB_SPLIT ${SMMU_STRTAB_SPLIT} cannot exceed "
	"SMMU_MAX_SID_BITS ${SMMU_MAX_SID_BITS}\n")
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
    PRIVATE "SMMU_MAX_LOG2_CMDQ_SIZE=${SMMU_MAX_LOG2_CMDQ_SIZE}U")
target_compile_definitions(rmm-lib-smmuv3
    PRIVATE "SMMU_MAX_LOG2_EVTQ_SIZE=${SMMU_MAX_LOG2_EVTQ_SIZE}U")
target_compile_definitions(rmm-lib-smmuv3
    PRIVATE "SMMU_MAX_SID_BITS=${SMMU_MAX_SID_BITS}U")
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
    PRIVATE "src/${RMM_ARCH}/smmuv3.c")

#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-debug INTERFACE)

#
# Default log level is 20 for Release build and
# 40 for Debug build. Modify this config to change
# LOG_LEVEL.
#
arm_config_option(
    NAME LOG_LEVEL
    HELP "Log level to apply for RMM (0 - 50)"
    TYPE STRING
    DEFAULT UNSET)


if(NOT LOG_LEVEL STREQUAL UNSET)
    target_compile_definitions(rmm-lib-debug
      INTERFACE "LOG_LEVEL=${LOG_LEVEL}")
endif()

target_include_directories(rmm-lib-debug
    INTERFACE "include")

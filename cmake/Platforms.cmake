#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Load in the platform based on its source directory.
#

arm_config_option(
    NAME RMM_PLATFORM
    HELP "Platform to build."
    TYPE PATH
    DEFAULT "" # Force a configuration failure if unset
    DEPENDS NOT RMM_PLATFORM
    ELSE "${RMM_PLATFORM}") # Maintain the value when it's forcibly hidden

set(RMM_PLATFORM_SOURCE_DIR "${CMAKE_SOURCE_DIR}/plat/${RMM_PLATFORM}")

if(NOT EXISTS ${RMM_PLATFORM_SOURCE_DIR})
    message(FATAL_ERROR "Cannot find ${RMM_PLATFORM_SOURCE_DIR}. Invalid platform specified")
endif()

#
# Load in the platform-specific list file.
#

add_subdirectory("${RMM_PLATFORM_SOURCE_DIR}")

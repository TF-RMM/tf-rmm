#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Set up the toolchain logic. This is only necessary if a toolchain file hasn't
# been provided. Otherwise, we force this option to an empty string.
#

if(DEFINED CACHE{CMAKE_TOOLCHAIN_FILE} AND NOT DEFINED RMM_TOOLCHAIN)
    message(WARNING
        "The RMM project does not support `CMAKE_TOOLCHAIN_FILE` directly. "
        "Please use `RMM_TOOLCHAIN` to configure your desired toolchain.")

    unset(CMAKE_TOOLCHAIN_FILE CACHE)
endif()

file(GLOB toolchains
    RELATIVE "${CMAKE_SOURCE_DIR}/toolchains/${RMM_ARCH}"
        "${CMAKE_SOURCE_DIR}/toolchains/${RMM_ARCH}/*.cmake")
string(REPLACE ".cmake" "" toolchains "${toolchains}")

arm_config_option(
    NAME RMM_TOOLCHAIN
    HELP "Toolchain name."
    STRINGS ${toolchains}
    DEFAULT ""
    DEPENDS (NOT RMM_TOOLCHAIN IN_LIST toolchains)
    ELSE "${RMM_TOOLCHAIN}")

if(NOT EXISTS CMAKE_TOOLCHAIN_FILE)
    set(CMAKE_TOOLCHAIN_FILE
        "${CMAKE_SOURCE_DIR}/toolchains/${RMM_ARCH}/${RMM_TOOLCHAIN}.cmake")
endif()

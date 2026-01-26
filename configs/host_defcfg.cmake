#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Set the RMM_PLATFORM variable to Cmake cache.
#
set(RMM_PLATFORM "host" CACHE STRING "platform")

arm_config_option_override(NAME RMM_ARCH DEFAULT "fake_host")
arm_config_option_override(NAME RMM_TOOLCHAIN DEFAULT "gnu")

#
# Width of the virtual address space for the system.
#
arm_config_option_override(NAME VIRT_ADDR_SPACE_WIDTH DEFAULT 38)

#
# Set RMM_MAX_SIZE for this platform.
#
arm_config_option_override(NAME RMM_MAX_SIZE DEFAULT 0x01000000)

#
# Disable RMM_EL3_COMPAT_RESERVE_MEM
#
arm_config_option_override(NAME RMM_EL3_COMPAT_RESERVE_MEM DEFAULT FALSE)

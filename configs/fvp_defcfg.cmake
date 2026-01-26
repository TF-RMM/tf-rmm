#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Set the RMM_PLATFORM variable to Cmake cache.
#
set(RMM_PLATFORM "arm" CACHE STRING "platform")
arm_config_option_override(NAME RMM_TOOLCHAIN DEFAULT "gnu")

#
# Set RMM_MAX_SIZE for this platform (24MB)
#
arm_config_option_override(NAME RMM_MAX_SIZE DEFAULT 0x01800000)

#
# Disable RMM_EL3_COMPAT_RESERVE_MEM
#
arm_config_option_override(NAME RMM_EL3_COMPAT_RESERVE_MEM DEFAULT FALSE)

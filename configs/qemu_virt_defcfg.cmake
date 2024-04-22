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

# Maximum number of translation tables allocated by the runtime context
# for the translation library.
#
arm_config_option_override(NAME PLAT_CMN_CTX_MAX_XLAT_TABLES DEFAULT 7)

#
# Maximum number of granules supported.
#
arm_config_option_override(NAME RMM_MAX_GRANULES DEFAULT 0x100000)

#
# TF-A sets a limit of 32 CPUs for the QEMU virt platform.
#
arm_config_option_override(NAME MAX_CPUS DEFAULT 32)

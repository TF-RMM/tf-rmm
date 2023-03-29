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
# Maximum number of translation tables allocated by the runtime context
# for the translation library.
#
arm_config_option_override(NAME PLAT_CMN_CTX_MAX_XLAT_TABLES DEFAULT 6)

#
# Maximum number of granules supported, enough to cover 2GB of DDR0.
#
arm_config_option_override(NAME RMM_MAX_GRANULES DEFAULT 0x80000)

#
# Add a large number of MMAP regions to exercise unittests on xlat lib.
#
arm_config_option_override(NAME PLAT_CMN_MAX_MMAP_REGIONS DEFAULT 0xff)

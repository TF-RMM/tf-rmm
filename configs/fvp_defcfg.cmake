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
# Maximum number of translation tables allocated by the runtime context
# for the translation library.
#
arm_config_option_override(NAME PLAT_CMN_CTX_MAX_XLAT_TABLES DEFAULT 6)

#
# Maximum number of granules supported, enough to cover
# (2GB - 64MB) of DRAM0 and 2GB of DRAM1. We overprovision
# for the case that DT has not catered for the 64 MB carveout.
#
arm_config_option_override(NAME RMM_MAX_GRANULES DEFAULT 0x100000)

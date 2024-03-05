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
# Set RMM_MAX_SIZE for this platform (36MB)
#
arm_config_option_override(NAME RMM_MAX_SIZE DEFAULT 0x02400000)

#
# Maximum number of translation tables allocated by the runtime context
# for the translation library.
#
arm_config_option_override(NAME PLAT_CMN_CTX_MAX_XLAT_TABLES DEFAULT 6)

#
# Maximum number of granules supported, enough to cover (2GB - 128MB) of DRAM0
# and 6GB DRAM1.
#
arm_config_option_override(NAME RMM_MAX_GRANULES DEFAULT 0x1FBA00)

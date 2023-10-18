#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Set the RMM_PLATFORM variable to Cmake cache.
#
set(RMM_PLATFORM "qemu" CACHE STRING "platform")
arm_config_option_override(NAME RMM_TOOLCHAIN DEFAULT "gnu")

#
# Width of the virtual address space for the system.
#
arm_config_option_override(NAME VIRT_ADDR_SPACE_WIDTH DEFAULT 38)

#
# Set RMM_MAX_SIZE for this platform (24MB)
#
arm_config_option_override(NAME RMM_MAX_SIZE DEFAULT 0x01800000)

#
# UART Base address. This must be dynamically discovered in future.
# Use NS UART.
#
arm_config_option_override(NAME RMM_UART_ADDR DEFAULT 0x09000000)

#
# Extra memory regions needed by this platform: one region for UART.
#
arm_config_option_override(NAME PLAT_CMN_EXTRA_MMAP_REGIONS DEFAULT 1)

#
# Maximum number of translation tables allocated by the runtime context
# for the translation library.
#
arm_config_option_override(NAME PLAT_CMN_CTX_MAX_XLAT_TABLES DEFAULT 7)

#
# Disable FPU/SIMD usage in RMM for now. Enabling this causes the Realm guest
# boot to hang, and needs to be investigated.
#
arm_config_option_override(NAME RMM_FPU_USE_AT_REL2 DEFAULT OFF)

#
# Maximum number of granules supported.
#
arm_config_option_override(NAME RMM_MAX_GRANULES DEFAULT 0x100000)

#
# TF-A sets a limit of 32 CPUs for the QEMU virt platform.
#
arm_config_option_override(NAME MAX_CPUS DEFAULT 32)

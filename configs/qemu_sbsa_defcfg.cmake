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
# Set RMM_MAX_SIZE for this platform (1072MB).  Needs to be kept in sync with
# TF-A's REALM_DRAM_SIZE in platform_def.h.
#
arm_config_option_override(NAME RMM_MAX_SIZE DEFAULT 0x43000000)

#
# UART Base address. This must be dynamically discovered in future.
# Use NS UART.
#
arm_config_option_override(NAME RMM_UART_ADDR DEFAULT 0x60000000)

#
# Extra memory regions needed by this platform: one region for UART.
#
arm_config_option_override(NAME PLAT_CMN_EXTRA_MMAP_REGIONS DEFAULT 1)

#
# Maximum number of translation tables allocated by the runtime context
# for the translation library.
#
arm_config_option_override(NAME PLAT_CMN_CTX_MAX_XLAT_TABLES DEFAULT 9)

#
# Disable FPU/SIMD usage in RMM for now. Enabling this causes the Realm guest
# boot to hang, and needs to be investigated.
#
arm_config_option_override(NAME RMM_FPU_USE_AT_REL2 DEFAULT OFF)

#
# Maximum number of granules supported.  Needs to be kept in sync with
# TF-A's PLAT_QEMU_L1_GPT_SIZE in platform_def.h.  For SBSA we currently
# support a maximum of 1TB, which is 1024 L1GPTs plus another L1GPT for
# miscellaneous mapping, for a total of 1025 L1GPTs.  Each L1GPT maps 1GB,
# which yields 262144 GPT entries (GPTEs) per table, for a total of
# 0x10040000 granules.
#
arm_config_option_override(NAME RMM_MAX_GRANULES DEFAULT 0x10040000)

#
# TF-A sets a limit of 512 CPUs for the QEMU SBSA platform. See
# PLATFORM_MAX_CPUS_PER_CLUSTER and PLATFORM_CLUSTER_COUNT in file
# plat/qemu/qemu_sbsa/include/platform_def.h
#
arm_config_option_override(NAME MAX_CPUS DEFAULT 512)

#
# The SBSA's RAM starts at 1TB and the RMM code is located at that address.
# As such we need to set this to at least 41, which also means that a VM can
# have at most 1TB of RAM.
#
arm_config_option_override(NAME PLAT_CMN_VIRT_ADDR_SPACE_WIDTH DEFAULT 41)

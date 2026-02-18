#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Option to make PL011 SBSA compliant. Typically only enabled in
# hardware validation environments.
#
arm_config_option(
	NAME PL011_GENERIC_SBSA_UART
	HELP "Enable Generic (SBSA Compliant) PL011. This a subset of PL011 UART"
	STRINGS "ON" "OFF"
	DEFAULT "OFF")

arm_config_option(
	NAME PL011_HW_FLOW_CONTROL
	HELP "Enable Hardware Flow Control (RTS/CTS) for PL011 UART"
	STRINGS "ON" "OFF"
	DEFAULT "OFF")

add_library(rmm-driver-pl011)

target_link_libraries(rmm-driver-pl011
    PRIVATE rmm-lib)

if(PL011_GENERIC_SBSA_UART)
    target_compile_definitions(rmm-driver-pl011
        PUBLIC "PL011_GENERIC_SBSA_UART=1")
endif()

if(PL011_HW_FLOW_CONTROL)
    target_compile_definitions(rmm-driver-pl011
        PUBLIC "PL011_HW_FLOW_CONTROL=1")
endif()

target_include_directories(rmm-driver-pl011
    PUBLIC "include")

target_sources(rmm-driver-pl011
    PRIVATE "src/pl011.c")

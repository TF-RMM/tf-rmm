#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-driver-pl011)

target_link_libraries(rmm-driver-pl011
    PRIVATE rmm-lib)

arm_config_option(
    NAME RMM_UART_ADDR
    HELP "Physical UART address"
    TYPE STRING
    DEFAULT 0x0)

if(RMM_UART_ADDR EQUAL 0x0)
    message(FATAL_ERROR "RMM_UART_ADDR is not initialized")
endif()

target_compile_definitions(rmm-driver-pl011
    PUBLIC "RMM_UART_ADDR=ULL(${RMM_UART_ADDR})")

target_include_directories(rmm-driver-pl011
    PUBLIC "include")

target_sources(rmm-driver-pl011
    PRIVATE "src/pl011.c")

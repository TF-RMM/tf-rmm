/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PL011_H
#define PL011_H

#include <stdint.h>

/*
 * Function that initiates PL011 for console output
 * Arguments:
 *   base_addr - UART base address
 *   uart_clk  - UART input clock which sets master trasmit/receive rate
 *   baud_rate - UART Baudrate
 * Returns:
 *   0 on success or -EINVAL when invalid base address/clock/baud is used
 */
int pl011_init(uintptr_t base_addr, unsigned int uart_clk,
		unsigned int baud_rate);

#endif /* PL011_H */

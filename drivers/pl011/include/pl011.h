/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PL011_H
#define PL011_H

#include <stdint.h>

/* PL011 Registers */
#define UARTDR			0x00U
#define UARTECR			0x04U
#define UARTFR			0x18U

/* PL011 registers (out of the SBSA specification) */
#define UARTIBRD		0x24U
#define UARTFBRD		0x28U
#define UARTLCR_H		0x2CU
#define UARTCR			0x30U

/* Flag reg bits */

/* Transmit FIFO full */
#define PL011_UARTFR_TXFF	(1UL << 5)

/* Control reg bits */
#define PL011_UARTCR_RXE	(1UL << 9)	/* Receive enable */
#define PL011_UARTCR_TXE	(1UL << 8)	/* Transmit enable */
#define PL011_UARTCR_UARTEN	(1UL << 0)	/* UART Enable */

/* FIFO Enabled / No Parity / 8 Data bit / One Stop Bit */
#define PL011_LINE_CONTROL	(PL011_UARTLCR_H_FEN | PL011_UARTLCR_H_WLEN_8)

/* Line Control Register Bits */
#define PL011_UARTLCR_H_WLEN_8	(3UL << 5)
#define PL011_UARTLCR_H_FEN	(1UL << 4)	/* FIFOs Enable */

/*
 * Function that initiates UART for console output
 * Arguments:
 *   base_addr - UART base address
 *   uart_clk  - UART input clock which sets master trasmit/receive rate
 *   baud_rate - UART Baudrate
 * Returns:
 *   0 on success or -1 when invalid baseaddr/clock/baud is used
 */
int uart_init(uintptr_t base_addr, unsigned int uart_clk,
		unsigned int baud_rate);

#endif /* PL011_H */

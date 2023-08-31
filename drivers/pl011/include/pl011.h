/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PL011_H
#define PL011_H

#include <stdint.h>

/* PL011 Registers */
#define UARTDR                    0x000
#define UARTECR                   0x004
#define UARTFR                    0x018

/* PL011 registers (out of the SBSA specification) */
#define UARTIBRD                  0x024
#define UARTFBRD                  0x028
#define UARTLCR_H                 0x02C
#define UARTCR                    0x030

/* Flag reg bits */
#define PL011_UARTFR_TXFF         (1U << 5)	/* Transmit FIFO full */

/* Control reg bits */
#define PL011_UARTCR_RXE          (1U << 9)	/* Receive enable */
#define PL011_UARTCR_TXE          (1U << 8)	/* Transmit enable */
#define PL011_UARTCR_UARTEN       (1U << 0)	/* UART Enable */

/* FIFO Enabled / No Parity / 8 Data bit / One Stop Bit */
#define PL011_LINE_CONTROL  (PL011_UARTLCR_H_FEN | PL011_UARTLCR_H_WLEN_8)

/* Line Control Register Bits */
#define PL011_UARTLCR_H_WLEN_8    (3U << 5)
#define PL011_UARTLCR_H_FEN       (1U << 4)	/* FIFOs Enable */

/*
 * Function that initiates UART for console output
 * Arguments:
 *   baseaddr - UART base address
 *   clock    - UART input clock which sets master trasmit/receive rate
 *   baud     - UART Baudrate
 * Returns:
 *   0 on success or -1 when invalid baseaddr/clock/baud is used
 */
int uart_init(uintptr_t baseaddr, unsigned int clock, unsigned int baud);

#endif /* PL011_H */

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <mmio.h>
#include <pl011.h>
#include <utils_def.h>

static inline void uart_wait(void)
{
	/* Wait until there is room in the Tx FIFO */
	while ((read32((void *)((RMM_UART_ADDR) + UARTFR))
				& PL011_UARTFR_TXFF) != 0U) {
		/* Do nothing */
	}
}

/* Function that initializes UART for console output */
int uart_init(uintptr_t base_addr,
		unsigned int uart_clk,
		unsigned int baud_rate)
{
	unsigned int div;

	/* Check Base address, baud rate and UART clock for sanity */

	if (base_addr == 0UL) {
		return -1;
	}

	if (uart_clk == 0U) {
		return -1;
	}

	if (baud_rate == 0U) {
		return -1;
	}

	/* Disable UART before programming */
	write32(0U, (void *)((RMM_UART_ADDR) + UARTCR));

	/* Program the baudrate */
	div = (uart_clk * 4)/baud_rate;

	/* IBRD = Divisor >> 6 */
	write32(div >> 6, (void *)((RMM_UART_ADDR) + UARTIBRD));

	/* FBRD = Divisor & 0x3F */
	write32(div & 0x3f, (void *)((RMM_UART_ADDR) + UARTFBRD));

	/* Enable FIFO and set word length, parity and number of stop bits */
	write32(PL011_LINE_CONTROL, (void *)((RMM_UART_ADDR) + UARTLCR_H));

	/* Clear any pending errors */
	write32(0U, (void *)((RMM_UART_ADDR) + UARTECR));

	/* Enable Tx, Rx, and UART overall */
	write32(PL011_UARTCR_RXE | PL011_UARTCR_TXE | PL011_UARTCR_UARTEN,
		(void *)((RMM_UART_ADDR) + UARTCR));
	return 0;
}

static void uart_putc(char ch)
{
	uart_wait();
	write8(ch, (void *)((RMM_UART_ADDR) + UARTDR));
}

/* Serial output - called from printf */
void _putchar(char ch)
{
	if (ch == '\n') {
		uart_putc('\r');
	}
	uart_putc(ch);
}

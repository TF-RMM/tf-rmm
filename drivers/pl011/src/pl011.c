/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <console.h>
#include <errno.h>
#include <mmio.h>
#include <pl011.h>
#include <utils_def.h>

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
#define PL011_UARTFR_TXFF	(U(1) << 5)

/* Control reg bits */
#define PL011_UARTCR_RXE	(U(1) << 9)	/* Receive enable */
#define PL011_UARTCR_TXE	(U(1) << 8)	/* Transmit enable */
#define PL011_UARTCR_UARTEN	(U(1) << 0)	/* UART Enable */

/* FIFO Enabled / No Parity / 8 Data bit / One Stop Bit */
#define PL011_LINE_CONTROL	(PL011_UARTLCR_H_FEN | PL011_UARTLCR_H_WLEN_8)

/* Line Control Register Bits */
#define PL011_UARTLCR_H_WLEN_8	(U(3) << 5)
#define PL011_UARTLCR_H_FEN	(U(1) << 4)	/* FIFOs Enable */

static inline void pl011_wait(uintptr_t base)
{
	/* Wait until there is room in the Tx FIFO */
	while ((read32((void *)(base + UARTFR))
				& PL011_UARTFR_TXFF) != 0U) {
		/* Do nothing */
	}
}

static void writechar(uintptr_t base, int ch)
{
	pl011_wait(base);
	write8((uint8_t)ch, (void *)(base + UARTDR));
}

/* Serial output - called from console driver */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
static int pl011_putc(int c, const struct console *csl)
{
	assert(csl != NULL);

	if ((char)c == '\n') {
		/* NOLINTNEXTLINE(google-readability-casting) */
		writechar(csl->base, (int)'\r');
	}
	writechar(csl->base, c);

	return c;
}

static struct console pl011_csl = {
	.putc = pl011_putc,
	.flush = NULL
};

/* Function that initializes PL011 for console output */
int pl011_init(uintptr_t base_addr,
		unsigned int uart_clk,
		unsigned int baud_rate)
{
	unsigned int div;

	/* Check Base address, baud rate and UART clock for sanity */
	if ((base_addr == 0UL) || (uart_clk == 0U) ||
		(baud_rate == 0U)) {
		return -EINVAL;
	}

	/* Disable UART before programming */
	write32(0U, (void *)(base_addr + UARTCR));

	/* Program the baud rate */
	div = (uart_clk * 4U) / baud_rate;

	/* IBRD = Divisor >> 6 */
	write32(div >> 6, (void *)((base_addr) + UARTIBRD));

	/* FBRD = Divisor & 0x3F */
	write32(div & 0x3fU, (void *)((base_addr) + UARTFBRD));

	/* Enable FIFO and set word length, parity and number of stop bits */
	write32(PL011_LINE_CONTROL, (void *)((base_addr) + UARTLCR_H));

	/* Clear any pending errors */
	write32(0U, (void *)((base_addr) + UARTECR));

	/* Enable Tx, Rx, and UART overall */
	write32(PL011_UARTCR_RXE | PL011_UARTCR_TXE | PL011_UARTCR_UARTEN,
		(void *)((base_addr) + UARTCR));

	pl011_csl.base = base_addr;

	return console_register(&pl011_csl);
}

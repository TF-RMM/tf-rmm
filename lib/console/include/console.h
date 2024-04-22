/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

#ifndef CONSOLE_H
#define CONSOLE_H

#include <utils_def.h>

/* Console scope flags - unused now */
#define CONSOLE_FLAG_BOOT		(UL(1) << U(0))
#define CONSOLE_FLAG_RUNTIME		(UL(1) << U(1))
#define CONSOLE_FLAG_CRASH		(UL(1) << U(2))

/* Bits 3 to 7 reserved for additional scopes in future expansion. */
#define CONSOLE_FLAG_SCOPE_MASK		((UL(1) << U(8)) - U(1))

struct console {
	struct console *next;
	uint64_t flags;
	int (*const putc)(int character, const struct console *console);
	void (*const flush)(const struct console *console);
	uintptr_t base;

	/* Additional private driver data may follow here. */
};

/*
 * Add a console_t instance to the console list. This should only be called by
 * console drivers after they have initialized all fields in the console
 * structure.
 */
int console_register(struct console *csl);

/* Output a character on all consoles registered for the current state. */
int console_putc(int c);

/* Flush all consoles registered for the current state. */
void console_flush(void);

#endif /* CONSOLE_H */

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

#include <assert.h>
#include <console.h>
#include <errno.h>
#include <stddef.h>

/*
 * TF-RMM does not support multi-console yet. If this is a requirement, then
 * this driver needs to be enhanced.
 */
static struct console *console_head;

/*
 * This function is not meant to be called directly by platform, but rather
 * via the UART driver. Hence we can rely on the arguments being passed at runtime.
 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
int console_register(struct console *csl)
{
	assert(csl != NULL);

	/* Return error if console already registered */
	if (console_head != NULL) {
		return -EINVAL;
	}

	console_head = csl;
	return 0;
}

/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
int console_putc(int c)
{
	struct console *csl = console_head;

	/*
	 * If no console is registered or putc callback is NULL for the console,
	 * then return.
	 */
	if ((csl == NULL) || (csl->putc == NULL)) {
		return c;
	}

	/* Ignore the console state */
	return csl->putc(c, csl);
}

/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
void console_flush(void)
{
	struct console *csl = console_head;

	/*
	 * If no console is registered or flush callback is NULL for the console,
	 * then return.
	 */
	if ((csl == NULL) || (csl->flush == NULL)) {
		return;
	}

	csl->flush(csl);
}

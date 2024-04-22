/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <console.h>
#include <errno.h>
#include <host_console.h>
#include <stdio.h>

/* Serial output - called from console driver */
static int host_csl_putc(int c, const struct console *csl)
{
	assert(csl != NULL);
	return putchar(c);
}

static struct console host_csl = {
	.putc = host_csl_putc,
	.flush = NULL
};

/* Dummy console_init */
int host_csl_init(void)
{
	(void)console_register(&host_csl);
	return 0;
}

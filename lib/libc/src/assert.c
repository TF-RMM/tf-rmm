/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>

void __assert_func(const char *file, int line, const char *func, const char *expression)
{
	ERROR("Assertion \"%s\" failed %s:%d, %s\n", expression, file, line, func);
	while (true) {
		wfe();
	}
}

void __assert_fail(const char *expression, const char *file, unsigned int line, const char *func)
{
	/* Ignore func as it can be NULL */
	(void)func;
	ERROR("Assertion \"%s\" failed %s:%d\n", expression, file, line);
	while (true) {
		wfe();
	}
}

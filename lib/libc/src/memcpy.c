/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <stddef.h>
#include <string.h>

void *memcpy(void *dst, const void *src, size_t len)
{
	const char *s = src;
	char *d = dst;

	while (len != 0U) {
		*d = *s;
		len--;

		/* Do not form an unrepresentable one-past pointer. */
		if (len != 0U) {
			d++;
			s++;
		}
	}

	return dst;
}

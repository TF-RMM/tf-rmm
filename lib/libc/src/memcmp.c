/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <stddef.h>
#include <string.h>

int memcmp(const void *s1, const void *s2, size_t len)
{
	const unsigned char *s = s1;
	const unsigned char *d = s2;
	unsigned char sc;
	unsigned char dc;

	while (len--) {
		sc = *s++;
		dc = *d++;
		if (sc - dc) {
			return (sc - dc);
		}
	}

	return 0;
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <string.h>

size_t strlen(const char *s)
{
	const char *cursor = s;

	while (*cursor) {
		cursor++;
	}

	return cursor - s;
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Jon Medhurst <tixy@linaro.org>
 */

#include <stddef.h>
#include <string.h>

void *memmove(void *dst, const void *src, size_t len)
{
	/*
	 * Check whether dst is before src first so address subtraction cannot
	 * underflow. Otherwise, the subtraction safely determines whether dst
	 * begins outside the source data without computing src + len, which
	 * could overflow.
	 */
	if (((size_t)dst < (size_t)src) || (((size_t)dst - (size_t)src) >= len)) {
		/* destination not in source data, so can safely use memcpy */
		return memcpy(dst, src, len);
	}

	/* copy backwards... */
	const char *end = dst;
	const char *s = (const char *)src + len;
	char *d = (char *)dst + len;

	while (d != end) {
		*--d = *--s;
	}
	return dst;
}

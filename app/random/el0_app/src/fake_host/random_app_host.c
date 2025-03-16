/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

 #include <stddef.h>
 #include <utils_def.h>

size_t get_heap_page_count(void)
{
	return HEAP_PAGE_COUNT;
}
/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <stdbool.h>
#include <tb_common.h>
#include <xlat_high_va.h>

struct xlat_ctx *xlat_get_high_va_xlat_ctx(void)
{
	ASSERT(false, "xlat_get_high_va_xlat_ctx");
	return 0;
}

int xlat_high_va_setup(struct xlat_mmap_region *mm, unsigned int regions)
{
	ASSERT(false, "xlat_high_va_setup");
	return 0;
}

#endif /* CBMC */

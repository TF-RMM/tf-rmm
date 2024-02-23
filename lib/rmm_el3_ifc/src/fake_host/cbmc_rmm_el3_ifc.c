/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <stdbool.h>
#include <tb_common.h>

unsigned int rmm_el3_ifc_get_version(void)
{
	ASSERT(false, "rmm_el3_ifc_get_version");
	return 0;
}

#endif /* CBMC */

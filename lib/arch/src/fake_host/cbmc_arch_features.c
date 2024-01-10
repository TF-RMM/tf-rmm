/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>

#ifdef CBMC
#include <tb_common.h>

unsigned int arch_feat_get_pa_width(void)
{
	return 32U;
}

#endif

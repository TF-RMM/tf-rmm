/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef FEATURE_H
#define FEATURE_H

#include <smc-rmi.h>
#include <stdbool.h>
#include <utils_def.h>

unsigned long get_feature_register_0(void);

/* Check if DA is enabled in RMI feature register */
static inline bool is_rmi_feat_da_enabled(void)
{
	return (EXTRACT(RMI_FEATURE_REGISTER_0_DA_EN,
			get_feature_register_0()) == RMI_FEATURE_TRUE);
}

#endif /* FEATURE_H */

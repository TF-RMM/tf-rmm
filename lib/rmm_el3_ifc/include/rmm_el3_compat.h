/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RMM_EL3_COMPAT_H
#define RMM_EL3_COMPAT_H

#include <rmm_el3_ifc.h>

struct rmm_el3_compat_callbacks {
	int (*reserve_mem_cb)(size_t size, uint64_t *arg);
};

void rmm_el3_ifc_set_compat_callbacks(
		struct rmm_el3_compat_callbacks *callbacks);

#endif /* RMM_EL3_COMPAT_H */

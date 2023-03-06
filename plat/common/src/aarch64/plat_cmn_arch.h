/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PLAT_CMN_ARCH_H
#define PLAT_CMN_ARCH_H

#include <import_sym.h>

#define get_shared_buf_va(x)	RMM_SHARED_BUFFER_START
#define get_shared_buf_pa()	rmm_el3_ifc_get_shared_buf_pa()

#endif /* PLAT_CMN_ARCH_H */

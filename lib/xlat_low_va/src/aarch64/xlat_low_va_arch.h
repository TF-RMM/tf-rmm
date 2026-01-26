/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef XLAT_LOW_VA_ARCH_H
#define XLAT_LOW_VA_ARCH_H

#include <import_sym.h>
#include <mapped_va_arch.h>

#define get_shared_buf_pa()	rmm_el3_ifc_get_shared_buf_pa()

#endif /* XLAT_LOW_VA_ARCH_H */

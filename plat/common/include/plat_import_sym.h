/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PLAT_IMPORT_SYM_H
#define PLAT_IMPORT_SYM_H

#include <import_sym.h>

IMPORT_SYM(uintptr_t, rmm_text_start,		RMM_CODE_START);
IMPORT_SYM(uintptr_t, rmm_text_end,		RMM_CODE_END);
IMPORT_SYM(uintptr_t, rmm_ro_start,		RMM_RO_START);
IMPORT_SYM(uintptr_t, rmm_ro_end,		RMM_RO_END);
IMPORT_SYM(uintptr_t, rmm_rw_start,		RMM_RW_START);
IMPORT_SYM(uintptr_t, rmm_rw_end,		RMM_RW_END);

/*
 * Leave an invalid page between the end of RMM memory and the beginning
 * of the shared buffer VA. This will help to detect any memory access
 * underflow by RMM.
 */
#define RMM_SHARED_BUFFER_START	(RMM_RW_END + SZ_4K)

#endif /* PLAT_IMPORT_SYM_H */

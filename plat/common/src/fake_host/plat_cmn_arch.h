/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PLAT_CMN_ARCH_H
#define PLAT_CMN_ARCH_H

#include <import_sym.h>

/*
 * Define dummy symbols for fake_host build.
 * These must be defined as constant qualifiers for IMPORT_SYM to work.
 */
#define rmm_text_start	0x10000000UL
#define rmm_text_end	0x20000000UL
#define rmm_ro_start	0x20000000UL
#define rmm_ro_end	0x40000000UL
#define rmm_rw_start	0x40000000UL
#define rmm_rw_end	0x50000000UL

/*
 * Since fake_host architecture does not have VA address translation, we
 * pass the same shared buf address as the VA to be used for access by users of
 * rmm-el3-ifc.
 */
#define get_shared_buf_va(x)	x

/*
 * The fake_host_architecture does not do any address translation. Provide a
 * dummy address for the shared PA. We do not use the real shared buf address
 * here as it may collide with the dummy values in mmap regions and cause
 * xlat_table init to fail.
 */
#define get_shared_buf_pa()	rmm_rw_end

#endif /* PLAT_CMN_ARCH_H */

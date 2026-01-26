/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef XLAT_LOW_VA_ARCH_H
#define XLAT_LOW_VA_ARCH_H

#include <import_sym.h>
#include <mapped_va_arch.h>

/*
 * Define dummy symbols for fake_host build.
 * These must be defined as constant qualifiers for IMPORT_SYM to work.
 */
#define rmm_text_start	0x2000000UL
#define rmm_text_end	0x4000000UL
#define rmm_ro_start	0x6000000UL
#define rmm_ro_end	0x8000000UL
#define rmm_rw_start	0xA000000UL
#define rmm_rw_end	0xC000000UL

/*
 * The fake_host_architecture does not do any address translation. Provide a
 * dummy address for the shared PA for setup xlat tables. We do not use the
 * real shared buf address here as it may collide with the dummy values
 * in mmap regions and cause xlat_table init to fail.
 */
#define get_shared_buf_pa()	rmm_rw_end

#endif /* XLAT_LOW_VA_ARCH_H */

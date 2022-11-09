/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef IMPORT_SYM_H
#define IMPORT_SYM_H

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
 * Emulates the import of an assembly or linker symbol as a C expression
 * with the specified type.
 */
#define IMPORT_SYM(type, sym, name) \
	static const __attribute__((unused)) type name = (type)(sym)

#endif /* IMPORT_SYM_H */

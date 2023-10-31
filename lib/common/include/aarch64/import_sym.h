/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef IMPORT_SYM_H
#define IMPORT_SYM_H

/*
 * Import an assembly or linker symbol as a C expression with the specified
 * type
 */
#define IMPORT_SYM(type, sym, name) \
	extern unsigned long (sym);\
	static const __attribute__((unused)) type name = (type) (void *)(&(sym))

#endif /* IMPORT_SYM_H */

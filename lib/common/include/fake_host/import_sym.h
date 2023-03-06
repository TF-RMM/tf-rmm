/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef IMPORT_SYM_H
#define IMPORT_SYM_H

/*
 * Emulates the import of an assembly or linker symbol as a C expression
 * with the specified type.
 */
#define IMPORT_SYM(type, sym, name) \
	static const __attribute__((unused)) type name = (type)(sym)

#endif /* IMPORT_SYM_H */

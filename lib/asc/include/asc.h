/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#ifndef ASC_H
#define ASC_H

void asc_mark_secure(unsigned long addr);
void asc_mark_nonsecure(unsigned long addr);

#endif /* ASC_H */

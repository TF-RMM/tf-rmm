/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef MAPPED_VA_ARCH_H
#define MAPPED_VA_ARCH_H

/*
 * On AArch64, virtual addresses are used directly for memory access.
 * On fake_host, physical addresses are used instead.
 */
#define MAPPED_VA_ARCH(_va, _pa)	(_va)

#endif /* MAPPED_VA_ARCH_H */

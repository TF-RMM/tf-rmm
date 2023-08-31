/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIZES_H
#define SIZES_H

#include <utils_def.h>

#define SZ_1K	(UL(1) << 10)
#define SZ_1M	(UL(1) << 20)
#define SZ_1G	(UL(1) << 30)

#define SZ_4K	(UL(4)  * SZ_1K)
#define SZ_16K	(UL(16) * SZ_1K)
#define SZ_64K	(UL(64) * SZ_1K)

#define SZ_2G	(UL(2)  * SZ_1G)
#define SZ_2M	(UL(2)  * SZ_1M)

#ifndef __ASSEMBLER__
#define BITS_PER_UL	((unsigned int)(8U * sizeof(unsigned long)))
#endif

#endif /* SIZES_H */

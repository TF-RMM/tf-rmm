/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_DEFS_H
#define HOST_DEFS_H

#include <utils_def.h>

/* Allocate 1GB of space to be used as physical granules */
#define HOST_MEM_SIZE			UL(0x40000000)

/* Total number of granules on the current platform */
#define HOST_NR_GRANULES		(HOST_MEM_SIZE/GRANULE_SIZE)

#endif /* HOST_DEFS_H */

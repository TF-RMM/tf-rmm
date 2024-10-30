/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_DEFS_H
#define HOST_DEFS_H

#include <utils_def.h>

/* Total number of DRAM granules on the current platform */
#define HOST_NR_GRANULES		(HOST_DRAM_SIZE/GRANULE_SIZE)

/* Total number of non-coherent device granules on the current platform */
#define HOST_NR_NCOH_GRANULES		(HOST_NCOH_DEV_SIZE/GRANULE_SIZE)

#endif /* HOST_DEFS_H */

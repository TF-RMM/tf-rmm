/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef FVP_PRIVATE_H
#define FVP_PRIVATE_H

/* Default number of CPUs per cluster */
#define	FVP_MAX_CPUS_PER_CLUSTER	4

/* Default number of threads per CPU */
#define	FVP_MAX_PE_PER_CPU		1

#define FVP_UART_BAUDRATE		115200
#define FVP_UART_CLK_IN_HZ		14745600

/* Base address, size and end address of DRAM0 (2GB - 64MB) of space */
#define FVP_DRAM0_BASE			UL(0x80000000)
#define FVP_DRAM0_SIZE			UL(0x7C000000)
#define FVP_DRAM0_END			(FVP_DRAM0_BASE + FVP_DRAM0_SIZE - 1UL)

/* Base address, size and end address for the DRAM1 2GB of space */
#define FVP_DRAM1_BASE			UL(0x880000000)
#define FVP_DRAM1_SIZE			UL(0x80000000)
#define FVP_DRAM1_END			(FVP_DRAM1_BASE + FVP_DRAM1_SIZE - 1UL)

/* Start index for DRAM1 */
#define	FVP_DRAM1_IDX			(FVP_DRAM0_SIZE / GRANULE_SIZE)

/* Total size of DRAM0 + DRAM1 */
#define FVP_DRAM_SIZE			(FVP_DRAM0_SIZE + FVP_DRAM1_SIZE)

/* Total number of granules on the current platform */
#define FVP_NR_GRANULES			(FVP_DRAM_SIZE / GRANULE_SIZE)

#endif /* FVP_PRIVATE_H */

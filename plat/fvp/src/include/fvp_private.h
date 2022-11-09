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

/* Base address and size for the DRAM0 (allocating 2GB of space) */
#define FVP_DRAM0_BASE			UL(0x80000000)
#define FVP_DRAM0_SIZE			UL(0x80000000)

/* Total number of granules on the current platform */
#define FVP_NR_GRANULES			(FVP_DRAM0_SIZE/GRANULE_SIZE)

#endif /* FVP_PRIVATE_H */

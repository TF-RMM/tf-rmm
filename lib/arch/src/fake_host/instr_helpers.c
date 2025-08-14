/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <string.h>

/*******************************************************************************
 * Mock DC ZVA, Data Cache Zero by VA instruction
 ******************************************************************************/
void dczva(uint64_t addr)
{
#ifndef CBMC
	(void)memset((void *)addr, 0,
		1U << (EXTRACT(DCZID_EL0_BS, read_dczid_el0()) + 2U));
#endif /* CBMC */
}

/*******************************************************************************
 * Mock DC ZVA, Data Cache Zero by VA instruction
 ******************************************************************************/
void dccipae(uint64_t addr)
{
	(void)addr; /* Avoid unused parameter error */
	return;
}

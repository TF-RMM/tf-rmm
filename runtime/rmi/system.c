/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#include <assert.h>
#include <smc-handler.h>
#include <smc-rmi.h>

COMPILER_ASSERT(RMI_ABI_VERSION_MAJOR <= 0x7FFFUL);
COMPILER_ASSERT(RMI_ABI_VERSION_MINOR <= 0xFFFFUL);

void smc_version(unsigned long rmi_version, struct smc_result *res)
{
	if (rmi_version != RMI_ABI_VERSION) {
		res->x[0] = RMI_ERROR_INPUT;
	} else {
		res->x[0] = RMI_SUCCESS;
	}

	res->x[1] = RMI_ABI_VERSION;
	res->x[2] = RMI_ABI_VERSION;
}

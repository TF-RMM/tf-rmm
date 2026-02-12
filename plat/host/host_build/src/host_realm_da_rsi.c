/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <host_realm.h>
#include <host_utils.h>
#include <smc-rsi.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static int host_realm_da_rsi_call1(unsigned long *rec_regs, unsigned long *rec_sp_el0)
{
	(void)rec_sp_el0;

	INFO("Realm: RSI_VDEV_GET_INFO completed\n");
	if (rec_regs[0] != RSI_SUCCESS) {
		ERROR("RSI_VDEV_GET_INFO failed 0x%lx\n", rec_regs[0]);
		return RSI_ERROR_STATE;
	}

	return RSI_SUCCESS;
}

int host_realm_da_rsi_main(unsigned long *rec_regs, unsigned long *rec_sp_el0)
{
	(void)rec_sp_el0;

	INFO("Realm: Call RSI_VDEV_GET_INFO\n");

	/* Get device info */
	rec_regs[0] = SMC_RSI_VDEV_GET_INFO;
	rec_regs[1] = HOST_DA_VDEV_ID; /* VDEV id */
	rec_regs[2] = REALM_BUFFER_IPA; /* VDEV info buffer */

	return host_util_rsi_helper(host_realm_da_rsi_call1);
}

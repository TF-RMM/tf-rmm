/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <host_harness.h>
#include <smc.h>

unsigned long monitor_call(unsigned long id,
			unsigned long arg0,
			unsigned long arg1,
			unsigned long arg2,
			unsigned long arg3,
			unsigned long arg4,
			unsigned long arg5)
{
	return host_monitor_call(id, arg0, arg1, arg2, arg3, arg4, arg5);
}

void monitor_call_with_res(unsigned long id,
			   unsigned long arg0,
			   unsigned long arg1,
			   unsigned long arg2,
			   unsigned long arg3,
			   unsigned long arg4,
			   unsigned long arg5,
			   struct smc_result *res)
{
	host_monitor_call_with_res(id, arg0, arg1, arg2,
				   arg3, arg4, arg5, res);
}

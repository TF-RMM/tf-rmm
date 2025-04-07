/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <smc.h>
#include <stddef.h>

host_monitor_call_func host_monitor_call_ptr;
host_monitor_call_with_res_func host_monitor_call_with_res_ptr;

unsigned long monitor_call(unsigned long id,
			unsigned long arg0,
			unsigned long arg1,
			unsigned long arg2,
			unsigned long arg3,
			unsigned long arg4,
			unsigned long arg5)
{
	assert(host_monitor_call_ptr != NULL);
	return host_monitor_call_ptr(id, arg0, arg1, arg2, arg3, arg4, arg5);
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
	assert(host_monitor_call_with_res_ptr != NULL);
	host_monitor_call_with_res_ptr(id, arg0, arg1, arg2,
				   arg3, arg4, arg5, res);
}

void register_host_monitor_functions(
	host_monitor_call_func monitor_call,
	host_monitor_call_with_res_func monitor_call_with_res)
{
	host_monitor_call_ptr = monitor_call;
	host_monitor_call_with_res_ptr = monitor_call_with_res;
}

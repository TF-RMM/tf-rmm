/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <host_harness.h>
#include <smc.h>
#include <stddef.h>
#include <string.h>

unsigned long monitor_call(unsigned long id,
			unsigned long arg0,
			unsigned long arg1,
			unsigned long arg2,
			unsigned long arg3,
			unsigned long arg4,
			unsigned long arg5)
{
	struct smc_args args = { 0 };
	struct smc_result res = { 0 };

	args.v[0] = arg0;
	args.v[1] = arg1;
	args.v[2] = arg2;
	args.v[3] = arg3;
	args.v[4] = arg4;
	args.v[5] = arg5;

	host_monitor_call(id, &args, &res);

	return res.x[0];
}

void monitor_call_with_arg_res(unsigned long id, struct smc_args *args, struct smc_result *res)
{
	memset(res, 0, sizeof(*res));

	host_monitor_call(id, args, res);
}

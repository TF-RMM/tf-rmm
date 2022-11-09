/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <host_harness.h>
#include <run.h>

bool memcpy_ns_read(void *dest, const void *ns_src, unsigned long size)
{
	return host_memcpy_ns_read(dest, ns_src, size);
}


bool memcpy_ns_write(void *ns_dest, const void *src, unsigned long size)
{
	return host_memcpy_ns_write(ns_dest, src, size);
}

int run_realm(unsigned long *regs)
{
	return host_run_realm(regs);
}

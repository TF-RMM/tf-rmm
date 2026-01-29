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

bool memcpy_ns_read_4(void *dest, const void *ns_src)
{
	return host_memcpy_ns_read(dest, ns_src, 4U);
}

bool memcpy_ns_write_4(void *ns_dest, uint32_t value)
{
	uint32_t src = value;

	return host_memcpy_ns_write(ns_dest, &src, 4U);
}

int run_realm(unsigned long *regs, unsigned long *sp_el0)
{
	return host_run_realm(regs, sp_el0);
}

/*
 * On AArch64 these are assembly labels pointing to specific load/store
 * instructions used by the GPF trap handler.  On fake_host there are no
 * hardware-assisted traps, so the trap list is never consulted; we only need
 * the symbols to satisfy the linker.
 */
unsigned long ns_access_ret_0_func(void)
{
	return 0;
}
void *ns_access_ret_0 = ns_access_ret_0_func;

unsigned long ns_read_func(unsigned long realm_buf, unsigned long ns_buf, unsigned long len)
{
	(void)realm_buf;
	(void)ns_buf;
	(void)len;
	return 0;
}
void *ns_read = ns_read_func;

unsigned long ns_write_func(unsigned long ns_buf, unsigned long realm_buf, unsigned long len)
{
	(void)ns_buf;
	(void)realm_buf;
	(void)len;
	return 0;
}
void *ns_write = ns_write_func;

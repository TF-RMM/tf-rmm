/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <tb_common.h>

unsigned long ns_access_ret_0_func(void)
{
	ASSERT(false, "ns_access_ret_0");
	return 0;
}
void *ns_access_ret_0 = ns_access_ret_0_func;

unsigned long ns_read_func(unsigned long realm_buf, unsigned long ns_buf, unsigned long len)
{
	(void)realm_buf;
	(void)ns_buf;
	(void)len;
	ASSERT(false, "ns_read");
	return 0;
}
void *ns_read = ns_read_func;

unsigned long ns_write_func(unsigned long ns_buf, unsigned long realm_buf, unsigned long len)
{
	(void)ns_buf;
	(void)realm_buf;
	(void)len;
	ASSERT(false, "ns_write");
	return 0;
}
void *ns_write = ns_write_func;

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <host_utils.h>
#include <spinlock.h>
#include <string.h>

bool host_memcpy_ns_read(void *dest, const void *ns_src, unsigned long size)
{
	(void)memcpy(dest, ns_src, size);
	return true;
}

bool host_memcpy_ns_write(void *ns_dest, const void *src, unsigned long size)
{
	(void)memcpy(ns_dest, src, size);
	return true;
}

unsigned long host_monitor_call(unsigned long id,
			unsigned long arg0,
			unsigned long arg1,
			unsigned long arg2,
			unsigned long arg3,
			unsigned long arg4,
			unsigned long arg5)
{
	/* Avoid MISRA C:2102-2.7 warnings */
	(void)id;
	(void)arg0;
	(void)arg1;
	(void)arg2;
	(void)arg3;
	(void)arg4;
	(void)arg5;
	return 0UL;
}

void host_monitor_call_with_res(unsigned long id,
			unsigned long arg0,
			unsigned long arg1,
			unsigned long arg2,
			unsigned long arg3,
			unsigned long arg4,
			unsigned long arg5,
			struct smc_result *res)
{
	/* Avoid MISRA C:2102-2.7 warnings */
	(void)id;
	(void)arg0;
	(void)arg1;
	(void)arg2;
	(void)arg3;
	(void)arg4;
	(void)arg5;
	(void)res;
}

int host_run_realm(unsigned long *regs)
{
	/* Return an arbitrary exception */
	return ARM_EXCEPTION_SYNC_LEL;
}

void host_spinlock_acquire(spinlock_t *l)
{
	l->val = 1;
}

void host_spinlock_release(spinlock_t *l)
{
	l->val = 0;
}

u_register_t host_read_sysreg(char *reg_name)
{
	struct sysreg_cb *callbacks = host_util_get_sysreg_cb(reg_name);

	/*
	 * Return 0UL as default value for registers which do not have
	 * a read callback installed.
	 */
	if (callbacks == NULL) {
		return 0UL;
	}

	if (callbacks->rd_cb == NULL) {
		return 0UL;
	}

	return callbacks->rd_cb(callbacks->reg);
}

void host_write_sysreg(char *reg_name, u_register_t v)
{
	struct sysreg_cb *callbacks = host_util_get_sysreg_cb(reg_name);

	/*
	 * Ignore the write if the register does not have a write
	 * callback installed.
	 */
	if (callbacks != NULL) {
		if (callbacks->wr_cb != NULL) {
			callbacks->wr_cb(v, callbacks->reg);
		}
	}
}

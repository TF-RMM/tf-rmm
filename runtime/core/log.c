/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_helpers.h>
#include <debug.h>
#include <spinlock.h>
#include <stdarg.h>

#ifdef CBMC
void rmm_log(const char *fmt, ...)
{
	(void)fmt;
}
#else
static spinlock_t console_output_lock;

/* Logging for RMM EL2 core */
/* coverity[misra_c_2012_rule_5_8_violation:SUPPRESS] */
void rmm_log(const char *fmt, ...)
{
	va_list args;

	bool use_spinlock = is_mmu_enabled();

	/*
	 * The spinlock implementation relies on cache-coherent atomics that
	 * require the MMU to be enabled. Skip locking during early boot before
	 * the MMU is up; output may interleave in that window.
	 */
	if (use_spinlock) {
		spinlock_acquire(&console_output_lock);
	}

	va_start(args, fmt);
	(void)vprintf(fmt, args);
	va_end(args);

	if (use_spinlock) {
		spinlock_release(&console_output_lock);
	}
}
#endif /* CBMC */

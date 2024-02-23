/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#ifndef HOST_HARNESS_H
#define HOST_HARNESS_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <types.h>

/* Fake host wrapper to read and write sysregs */
u_register_t host_read_sysreg(char *reg_name);
void host_write_sysreg(char *reg_name, u_register_t v);

struct spinlock_s;
struct byte_spinlock_s;

/* Fake host harness to lock and release spin lock */
void host_spinlock_acquire(struct spinlock_s *l);
void host_spinlock_release(struct spinlock_s *l);
void host_byte_spinlock_acquire(struct byte_spinlock_s *l);
void host_byte_spinlock_release(struct byte_spinlock_s *l);

/*
 * Fake host Wrapper to copy data from NS into Realm memory. The function
 * returns true if the copy succeeds. If the access to the NS memory generates
 * a fault, false is returned to the caller. In case of failure
 * (when false is returned), partial data may have been written to the
 * destination buffer.
 *
 * Args:
 *    dest - The address of buffer in Realm memory to write into.
 *    ns_src - The address of buffer in NS memory to read from.
 *    size - The number of bytes to copy.
 *    All arguments must be aligned to 8 bytes.
 */

bool host_memcpy_ns_read(void *dest, const void *ns_src, unsigned long size);

/*
 * Fake host wrapper to copy data from Realm into NS memory.The function
 * returns true if the copy succeeds. If the access to the NS memory generates
 * a fault, false is returned to the caller. In case of failure (when false is
 * returned), partial data may have been written to the destination buffer.
 *
 * Args:
 *    ns_dest - The address of buffer in NS memory to write into.
 *    src - The address of buffer in Realm memory to read from.
 *    size - The number of bytes to copy.
 *    All arguments must be aligned to 8 bytes.
 */
bool host_memcpy_ns_write(void *ns_dest, const void *src, unsigned long size);

/*
 * Fake host wrapper to run a realm.
 * Args:
 *     regs - pointer to GP regs to be restored/save when entering/exiting
 *            Realm
 * Return: Realm exception syndrome return.
 */
int host_run_realm(unsigned long *regs);

/*
 * Fake Host wrapper for monitor_call.
 */
unsigned long host_monitor_call(unsigned long id, unsigned long arg0,
		unsigned long arg1, unsigned long arg2, unsigned long arg3,
		unsigned long arg4, unsigned long arg5);

struct smc_result;
/*
 * Fake Host wrapper for monitor_call_with_res.
 */
void host_monitor_call_with_res(unsigned long id, unsigned long arg0,
		unsigned long arg1, unsigned long arg2, unsigned long arg3,
		unsigned long arg4, unsigned long arg5,
		struct smc_result *res);

/*
 * Fake host wrapper to map a given PA.
 *
 * It returns the VA to which the buffer is mapped.
 */
void *host_buffer_arch_map(unsigned int slot, unsigned long addr);

/*
 * Fake host wrapper to unmap a buffer slot correspondig to the VA passed
 * in `buf`.
 */
void host_buffer_arch_unmap(void *buf);

/*
 * Fake host wrapper to delegate a granule using the Granule Transition Service
 */
unsigned long host_gtsi_delegate(unsigned long addr);

/*
 * Fake host wrapper to undelegate a granule using the Granule Transition Service
 */
unsigned long host_gtsi_undelegate(unsigned long addr);

#endif /* HOST_HARNESS_H */

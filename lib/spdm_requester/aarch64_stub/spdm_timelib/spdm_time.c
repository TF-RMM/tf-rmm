/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <library/requester/timelib.h>

/*
 * Suspends the execution of the current SPDM request called through RMI command
 * until the time-out interval elapses.
 *
 * duration -  The time interval for which execution is to be suspended, in
 *             microseconds.
 */
void libspdm_sleep(uint64_t duration)
{
	/*
	 * libspdm_sleep() is called from device IO communication path, when
	 * the device returns LIBSPDM_STATUS_BUSY_PEER. RMM needs to handle
	 * such libspdm_sleep by exit to NS host with RmiIoExit.timeout set?
	 * todo: For now define this function. Look at it when DA stack is run
	 * on aarch64 platform.
	 */
	(void)duration;
}

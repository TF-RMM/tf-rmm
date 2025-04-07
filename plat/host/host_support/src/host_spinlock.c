/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <spinlock.h>

void host_spinlock_acquire(spinlock_t *l)
{
	/*
	 * The fake_host architecture is single threaded and we do not expect
	 * the lock to be already acquired in properly implemented locking
	 * sequence.
	 */
	assert(l->val == 0);
	l->val = 1;
}

void host_spinlock_release(spinlock_t *l)
{
	l->val = 0;
}

void host_byte_spinlock_acquire(byte_spinlock_t *l)
{
	assert(l->val == 0);
	l->val = 1;
}

void host_byte_spinlock_release(byte_spinlock_t *l)
{
	l->val = 0;
}

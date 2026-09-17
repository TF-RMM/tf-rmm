/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <spinlock.h>

bool host_spinlock_try_acquire(spinlock_t *l)
{
	unsigned int expected = 0U;

	return __atomic_compare_exchange_n(&l->val, &expected, 1U, false,
					   __ATOMIC_ACQUIRE,
					   __ATOMIC_RELAXED);
}

void host_spinlock_wait(spinlock_t *l)
{
	while (__atomic_load_n(&l->val, __ATOMIC_RELAXED) != 0U) {
		/* The fake-host implementation does not model PE wait events. */
	}
}

void host_spinlock_acquire(spinlock_t *l)
{
	bool acquired;

	/*
	 * The fake_host architecture is single threaded and we do not expect
	 * the lock to be already acquired in properly implemented locking
	 * sequence.
	 */
	acquired = host_spinlock_try_acquire(l);
	assert(acquired);
	(void)acquired;
}

void host_spinlock_release(spinlock_t *l)
{
	assert(__atomic_load_n(&l->val, __ATOMIC_RELAXED) != 0U);
	__atomic_store_n(&l->val, 0U, __ATOMIC_RELEASE);
}

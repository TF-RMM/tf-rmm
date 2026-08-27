/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RWLOCK_H
#define RWLOCK_H

#include <assert.h>
#include <atomics.h>
#include <bitlock.h>
#include <memory.h>
#include <stdbool.h>
#include <stdint.h>
#include <utils_def.h>

#define RWLOCK_GATE_SHIFT	U(63)
#define RWLOCK_WRITER_SHIFT	U(62)
#define RWLOCK_GATE_BIT		(UL(1) << RWLOCK_GATE_SHIFT)
#define RWLOCK_WRITER_BIT	(UL(1) << RWLOCK_WRITER_SHIFT)
#define RWLOCK_READERS_MASK	(RWLOCK_WRITER_BIT - 1UL)

/*
 * Reader-writer lock encoded in one naturally aligned, atomic 64-bit word:
 * [63] admission gate, [62] writer active, [61:0] reader count.
 *
 * The gate serializes reader admission and excludes writers. Reader releases
 * update the count independently, so all changes must preserve unrelated bits.
 * Writers leave the gate open between attempts so existing readers can finish
 * nested lookups. Tracking transitions use the try operation to back off
 * without retaining any region or descriptor locks.
 */
typedef struct {
	uint64_t state;
} rwlock_t;

/*
 * Diagnostic snapshots of a non-NULL, initialized lock. Each helper evaluates
 * its argument once and uses a relaxed atomic load; it does not establish
 * ownership or synchronize accesses to protected data.
 */
#define RWLOCK_READERS(_lock)	\
	(__atomic_load_n(&(_lock)->state, __ATOMIC_RELAXED) & RWLOCK_READERS_MASK)

#define RWLOCK_GATE_LOCKED(_lock)	\
	((__atomic_load_n(&(_lock)->state, __ATOMIC_RELAXED) & RWLOCK_GATE_BIT) != 0UL)

#define RWLOCK_WRITER_LOCKED(_lock)	\
	((__atomic_load_n(&(_lock)->state, __ATOMIC_RELAXED) & RWLOCK_WRITER_BIT) != 0UL)

/* Initialize an unused reader-writer lock before publishing it to other PEs. */
static inline void rwlock_init(rwlock_t *lock)
{
	assert(lock != NULL);
	lock->state = 0UL;
}

/*
 * Acquire shared ownership with acquire ordering; pair every nested acquisition
 * with a release. The number of outstanding readers must fit in 62 bits.
 */
static inline void rwlock_read_acquire(rwlock_t *lock)
{
	assert(lock != NULL);
	bitlock_acquire_64(&lock->state, RWLOCK_GATE_SHIFT);
	assert(!RWLOCK_WRITER_LOCKED(lock));

	/* Only this gate owner can increment, so check before carrying into flags. */
	assert(RWLOCK_READERS(lock) < RWLOCK_READERS_MASK);
	atomic_add_64(&lock->state, 1UL);

	bitlock_release_64(&lock->state, RWLOCK_GATE_SHIFT);
}

/* Release one caller-owned reader with release ordering, without taking the gate. */
static inline void rwlock_read_release(rwlock_t *lock)
{
	assert(lock != NULL);
	/* Our outstanding reader prevents a valid release from borrowing from flags. */
	assert(RWLOCK_READERS(lock) != 0UL);
	(void)atomic_load_add_release_64(&lock->state, UINT64_MAX);
}

/*
 * Try to acquire exclusive ownership without waiting for readers or writers.
 * Inspect the reader count under the gate so a new reader cannot race a
 * successful acquisition. Its acquire load synchronizes with readers that
 * release after gate acquisition. Return true with the gate retained and the
 * diagnostic writer bit set, or false without retaining the gate.
 */
static inline bool rwlock_write_try_acquire(rwlock_t *lock)
{
	assert(lock != NULL);
	if (!bitlock_try_acquire_64(&lock->state, RWLOCK_GATE_SHIFT)) {
		return false;
	}
	if ((SCA_READ64_ACQUIRE(&lock->state) & RWLOCK_READERS_MASK) != 0UL) {
		bitlock_release_64(&lock->state, RWLOCK_GATE_SHIFT);
		return false;
	}
	assert(!RWLOCK_WRITER_LOCKED(lock));
	/* Ownership is established; record the diagnostic writer state. */
	atomic_bit_set_64(&lock->state, RWLOCK_WRITER_SHIFT);
	return true;
}

/*
 * Acquire exclusive ownership with acquire ordering. On contention, wait for
 * the state to change without retaining the gate, so readers can finish nested
 * acquisitions. The AArch64 wait uses an exclusive load and WFE to save power.
 */
static inline void rwlock_write_acquire(rwlock_t *lock)
{
	while (!rwlock_write_try_acquire(lock)) {
		uint64_t state = SCA_READ64(&lock->state);

		/* Retry immediately if the lock became free after the failed try. */
		if (state != 0UL) {
			bitlock_wait_while_64(&lock->state, UINT64_MAX, state);
		}
	}
}

/*
 * Release caller-owned exclusive access. The gate release publishes protected
 * updates and the preceding relaxed clear of the diagnostic writer bit.
 */
static inline void rwlock_write_release(rwlock_t *lock)
{
	assert((lock != NULL) && RWLOCK_WRITER_LOCKED(lock));
	/* Clear the writer bit before allowing the next reader to enter. */
	atomic_bit_clear_64(&lock->state, RWLOCK_WRITER_SHIFT);
	bitlock_release_64(&lock->state, RWLOCK_GATE_SHIFT);
}

/*
 * Return an atomic snapshot of the writer bit for diagnostics. This neither
 * establishes ownership by the calling PE nor synchronizes protected accesses.
 */
static inline bool rwlock_is_write_locked(const rwlock_t *lock)
{
	assert(lock != NULL);

	return RWLOCK_WRITER_LOCKED(lock);
}

#endif /* RWLOCK_H */

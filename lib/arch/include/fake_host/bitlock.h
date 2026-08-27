/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef BITLOCK_H
#define BITLOCK_H

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <utils_def.h>

/*
 * Try to atomically acquire an 8-bit field lock with acquire ordering.
 *
 * @loc must be non-NULL and naturally aligned for uint8_t.
 * @bit must be less than 8. Returns true when the bit was previously
 * clear and is now owned by the caller, or false when the bit was already set.
 */
static inline bool bitlock_try_acquire_8(uint8_t *loc, unsigned int bit)
{
	uint8_t mask;
	uint8_t old;

	assert((loc != NULL) && (bit < 8U));
	mask = (uint8_t)(1U << bit);
	old = __atomic_fetch_or(loc, mask, __ATOMIC_ACQUIRE);

	return (old & mask) == 0U;
}

/*
 * Wait while the masked 8-bit field equals @value, without acquiring it.
 *
 * @loc must be non-NULL and naturally aligned for uint8_t.
 * @mask must be nonzero and @value must contain only masked bits. Returns
 * when a relaxed load observes a different masked value.
 * The fake-host implementation does not model PE wait events.
 */
static inline void bitlock_wait_while_8(uint8_t *loc, uint8_t mask,
				       uint8_t value)
{
	assert((loc != NULL) && (mask != 0U) && ((value & mask) == value));

	while ((__atomic_load_n(loc, __ATOMIC_RELAXED) & mask) == value) {
		/* Retry until a masked bit changes. */
	}
}

/*
 * Wait until an 8-bit field lock is observed unlocked, without acquiring it.
 *
 * @loc must be non-NULL and naturally aligned for uint8_t.
 * @bit must be less than 8.
 */
static inline void bitlock_wait_8(uint8_t *loc, unsigned int bit)
{
	uint8_t mask;

	assert((loc != NULL) && (bit < 8U));
	mask = (uint8_t)(1U << bit);
	bitlock_wait_while_8(loc, mask, mask);
}

/*
 * Acquire an 8-bit field lock with acquire memory ordering.
 *
 * @loc must be non-NULL and naturally aligned for uint8_t.
 * @bit must be less than 8 and initially clear; contention cannot progress
 * in the single-thread host. Return with the selected bit owned by the caller.
 */
static inline void bitlock_acquire_8(uint8_t *loc, unsigned int bit)
{
	bool acquired;

	assert((loc != NULL) && (bit < 8U));

	/* A contended lock cannot make progress in the single-thread host. */
	acquired = bitlock_try_acquire_8(loc, bit);
	assert(acquired);
	(void)acquired;
}

/*
 * Release an acquired 8-bit field lock with release ordering.
 *
 * @loc must be non-NULL and naturally aligned for uint8_t.
 * @bit must be less than 8 and the caller must own the selected bit lock.
 */
static inline void bitlock_release_8(uint8_t *loc, unsigned int bit)
{
	uint8_t mask;

	assert((loc != NULL) && (bit < 8U));
	mask = (uint8_t)(1U << bit);
	assert((__atomic_load_n(loc, __ATOMIC_RELAXED) & mask) != 0U);
	(void)__atomic_fetch_and(loc, (uint8_t)~mask, __ATOMIC_RELEASE);
}

/*
 * Try to atomically acquire a 16-bit field lock with acquire ordering.
 *
 * @loc must be non-NULL and naturally aligned for uint16_t.
 * @bit must be less than 16. Returns true when the bit was previously
 * clear and is now owned by the caller, or false when the bit was already set.
 */
static inline bool bitlock_try_acquire_16(uint16_t *loc, unsigned int bit)
{
	uint16_t mask;
	uint16_t old;

	assert((loc != NULL) && (bit < 16U));
	assert(ALIGNED((uintptr_t)loc, sizeof(*loc)));
	mask = (uint16_t)(1U << bit);
	old = __atomic_fetch_or(loc, mask, __ATOMIC_ACQUIRE);

	return (old & mask) == 0U;
}

/*
 * Wait while the masked 16-bit field equals @value, without acquiring it.
 *
 * @loc must be non-NULL and naturally aligned for uint16_t.
 * @mask must be nonzero and @value must contain only masked bits. Returns
 * when a relaxed load observes a different masked value.
 * The fake-host implementation does not model PE wait events.
 */
static inline void bitlock_wait_while_16(uint16_t *loc, uint16_t mask,
				       uint16_t value)
{
	assert((loc != NULL) && (mask != 0U) && ((value & mask) == value));
	assert(ALIGNED((uintptr_t)loc, sizeof(*loc)));

	while ((__atomic_load_n(loc, __ATOMIC_RELAXED) & mask) == value) {
		/* Retry until a masked bit changes. */
	}
}

/*
 * Wait until a 16-bit field lock is observed unlocked, without acquiring it.
 *
 * @loc must be non-NULL and naturally aligned for uint16_t.
 * @bit must be less than 16.
 */
static inline void bitlock_wait_16(uint16_t *loc, unsigned int bit)
{
	uint16_t mask;

	assert((loc != NULL) && (bit < 16U));
	assert(ALIGNED((uintptr_t)loc, sizeof(*loc)));
	/* cppcheck-suppress misra-c2012-12.2 */
	mask = (uint16_t)(1U << bit);
	bitlock_wait_while_16(loc, mask, mask);
}

/*
 * Acquire a 16-bit field lock with acquire memory ordering.
 *
 * @loc must be non-NULL and naturally aligned for uint16_t.
 * @bit must be less than 16 and initially clear; contention cannot progress
 * in the single-thread host. Return with the selected bit owned by the caller.
 */
static inline void bitlock_acquire_16(uint16_t *loc, unsigned int bit)
{
	bool acquired;

	assert((loc != NULL) && (bit < 16U));
	assert(ALIGNED((uintptr_t)loc, sizeof(*loc)));

	/* A contended lock cannot make progress in the single-thread host. */
	acquired = bitlock_try_acquire_16(loc, bit);
	assert(acquired);
	(void)acquired;
}

/*
 * Release an acquired 16-bit field lock with release ordering.
 *
 * @loc must be non-NULL and naturally aligned for uint16_t.
 * @bit must be less than 16 and the caller must own the selected bit lock.
 */
static inline void bitlock_release_16(uint16_t *loc, unsigned int bit)
{
	uint16_t mask;

	assert((loc != NULL) && (bit < 16U));
	assert(ALIGNED((uintptr_t)loc, sizeof(*loc)));
	mask = (uint16_t)(1U << bit);
	assert((__atomic_load_n(loc, __ATOMIC_RELAXED) & mask) != 0U);
	(void)__atomic_fetch_and(loc, (uint16_t)~mask, __ATOMIC_RELEASE);
}

/*
 * Try to atomically acquire a 64-bit field lock with acquire ordering.
 *
 * @loc must be non-NULL and naturally aligned for uint64_t.
 * @bit must be less than 64. Returns true when the bit was previously
 * clear and is now owned by the caller, or false when the bit was already set.
 */
static inline bool bitlock_try_acquire_64(uint64_t *loc, unsigned int bit)
{
	uint64_t mask;
	uint64_t old;

	assert((loc != NULL) && (bit < 64U));
	assert(ALIGNED((uintptr_t)loc, sizeof(*loc)));
	mask = (1UL << bit);
	old = __atomic_fetch_or(loc, mask, __ATOMIC_ACQUIRE);

	return (old & mask) == 0U;
}

/*
 * Wait while the masked 64-bit field equals @value, without acquiring it.
 *
 * @loc must be non-NULL and naturally aligned for uint64_t.
 * @mask must be nonzero and @value must contain only masked bits. Returns
 * when a relaxed load observes a different masked value.
 * The fake-host implementation does not model PE wait events.
 */
static inline void bitlock_wait_while_64(uint64_t *loc, uint64_t mask,
				       uint64_t value)
{
	assert((loc != NULL) && (mask != 0U) && ((value & mask) == value));
	assert(ALIGNED((uintptr_t)loc, sizeof(*loc)));

	while ((__atomic_load_n(loc, __ATOMIC_RELAXED) & mask) == value) {
		/* Retry until a masked bit changes. */
	}
}

/*
 * Wait until a 64-bit field lock is observed unlocked, without acquiring it.
 *
 * @loc must be non-NULL and naturally aligned for uint64_t.
 * @bit must be less than 64.
 */
static inline void bitlock_wait_64(uint64_t *loc, unsigned int bit)
{
	uint64_t mask;

	assert((loc != NULL) && (bit < 64U));
	assert(ALIGNED((uintptr_t)loc, sizeof(*loc)));
	mask = (1UL << bit);
	bitlock_wait_while_64(loc, mask, mask);
}

/*
 * Acquire a 64-bit field lock with acquire memory ordering.
 *
 * @loc must be non-NULL and naturally aligned for uint64_t.
 * @bit must be less than 64 and initially clear; contention cannot progress
 * in the single-thread host. Return with the selected bit owned by the caller.
 */
static inline void bitlock_acquire_64(uint64_t *loc, unsigned int bit)
{
	bool acquired;

	assert((loc != NULL) && (bit < 64U));
	assert(ALIGNED((uintptr_t)loc, sizeof(*loc)));

	/* A contended lock cannot make progress in the single-thread host. */
	acquired = bitlock_try_acquire_64(loc, bit);
	assert(acquired);
	(void)acquired;
}

/*
 * Release an acquired 64-bit field lock with release ordering.
 *
 * @loc must be non-NULL and naturally aligned for uint64_t.
 * @bit must be less than 64 and the caller must own the selected bit lock.
 */
static inline void bitlock_release_64(uint64_t *loc, unsigned int bit)
{
	uint64_t mask;

	assert((loc != NULL) && (bit < 64U));
	assert(ALIGNED((uintptr_t)loc, sizeof(*loc)));
	mask = (1UL << bit);
	assert((__atomic_load_n(loc, __ATOMIC_RELAXED) & mask) != 0U);
	(void)__atomic_fetch_and(loc, ~mask, __ATOMIC_RELEASE);
}

#endif /* BITLOCK_H */

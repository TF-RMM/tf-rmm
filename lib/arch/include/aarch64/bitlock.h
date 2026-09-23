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
	uint8_t old;
	uint8_t mask;

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
 * A conflicting store after the exclusive load generates an event, so an
 * unlock or a masked state change cannot be missed before WFE.
 *
 * The local exclusive monitor is cleared before returning.
 */
static inline void bitlock_wait_while_8(uint8_t *loc, uint8_t mask,
				       uint8_t value)
{
	uint32_t tmp;

	assert((loc != NULL) && (mask != 0U) && ((value & mask) == value));

	/* cppcheck-suppress misra-c2012-17.3 */
	asm volatile(
	"1:	ldxrb	%w[tmp], %[lock]\n"
	"	and	%w[tmp], %w[tmp], %w[mask]\n"
	"	cmp	%w[tmp], %w[value]\n"
	"	b.ne	2f\n"
	"	wfe\n"
	"	b	1b\n"
	"2:	clrex\n"
	: [tmp] "=&r" (tmp)
	: [lock] "Q" (*loc),
	  [mask] "r" ((uint32_t)mask),
	  [value] "r" ((uint32_t)value)
	: "cc", "memory"
	);
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
 * @bit must be less than 8. Wait until the lock is observed clear before
 * attempting the atomic update, avoiding an LSE operation while the lock is
 * known to be held. Returns with the selected bit lock owned by the caller.
 */
static inline void bitlock_acquire_8(uint8_t *loc, unsigned int bit)
{
	assert((loc != NULL) && (bit < 8U));

	do {
		bitlock_wait_8(loc, bit);
	} while (!bitlock_try_acquire_8(loc, bit));
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
	uint16_t old;
	uint16_t mask;

	assert((loc != NULL) && (bit < 16U));
	assert(ALIGNED((uintptr_t)loc, sizeof(*loc)));
	/* cppcheck-suppress misra-c2012-12.2 */
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
 * A conflicting store after the exclusive load generates an event, so an
 * unlock or a masked state change cannot be missed before WFE.
 *
 * The local exclusive monitor is cleared before returning.
 */
static inline void bitlock_wait_while_16(uint16_t *loc, uint16_t mask,
				       uint16_t value)
{
	uint32_t tmp;

	assert((loc != NULL) && (mask != 0U) && ((value & mask) == value));
	assert(ALIGNED((uintptr_t)loc, sizeof(*loc)));

	/* cppcheck-suppress misra-c2012-17.3 */
	asm volatile(
	"1:	ldxrh	%w[tmp], %[lock]\n"
	"	and	%w[tmp], %w[tmp], %w[mask]\n"
	"	cmp	%w[tmp], %w[value]\n"
	"	b.ne	2f\n"
	"	wfe\n"
	"	b	1b\n"
	"2:	clrex\n"
	: [tmp] "=&r" (tmp)
	: [lock] "Q" (*loc),
	  [mask] "r" ((uint32_t)mask),
	  [value] "r" ((uint32_t)value)
	: "cc", "memory"
	);
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
 * @bit must be less than 16. Wait until the lock is observed clear before
 * attempting the atomic update, avoiding an LSE operation while the lock is
 * known to be held. Returns with the selected bit lock owned by the caller.
 */
static inline void bitlock_acquire_16(uint16_t *loc, unsigned int bit)
{
	assert((loc != NULL) && (bit < 16U));
	assert(ALIGNED((uintptr_t)loc, sizeof(*loc)));

	do {
		bitlock_wait_16(loc, bit);
	} while (!bitlock_try_acquire_16(loc, bit));
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
	/* cppcheck-suppress misra-c2012-12.2 */
	mask = (uint16_t)(1U << bit);
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
	uint64_t old;
	uint64_t mask;

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
 * A conflicting store after the exclusive load generates an event, so an
 * unlock or a masked state change cannot be missed before WFE.
 *
 * The local exclusive monitor is cleared before returning.
 */
static inline void bitlock_wait_while_64(uint64_t *loc, uint64_t mask,
				       uint64_t value)
{
	uint64_t tmp;

	assert((loc != NULL) && (mask != 0U) && ((value & mask) == value));
	assert(ALIGNED((uintptr_t)loc, sizeof(*loc)));

	/* cppcheck-suppress misra-c2012-17.3 */
	asm volatile(
	"1:	ldxr	%[tmp], %[lock]\n"
	"	and	%[tmp], %[tmp], %[mask]\n"
	"	cmp	%[tmp], %[value]\n"
	"	b.ne	2f\n"
	"	wfe\n"
	"	b	1b\n"
	"2:	clrex\n"
	: [tmp] "=&r" (tmp)
	: [lock] "Q" (*loc),
	  [mask] "r" (mask),
	  [value] "r" (value)
	: "cc", "memory"
	);
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
 * @bit must be less than 64. Wait until the lock is observed clear before
 * attempting the atomic update, avoiding an LSE operation while the lock is
 * known to be held. Returns with the selected bit lock owned by the caller.
 */
static inline void bitlock_acquire_64(uint64_t *loc, unsigned int bit)
{
	assert((loc != NULL) && (bit < 64U));
	assert(ALIGNED((uintptr_t)loc, sizeof(*loc)));

	do {
		bitlock_wait_64(loc, bit);
	} while (!bitlock_try_acquire_64(loc, bit));
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
	(void)__atomic_fetch_and(loc, ~mask, __ATOMIC_RELEASE);
}

#endif /* BITLOCK_H */

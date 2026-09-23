/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef MEMORY_H
#define MEMORY_H

#include <stddef.h>
#include <stdint.h>

/* Single-Copy Atomic 64-bit write */
static inline void __sca_write64(uint64_t *ptr, uint64_t val)
{
	*ptr = val;
}
#define SCA_WRITE64(_p, _v) __sca_write64((uint64_t *)(_p), ((uint64_t)(_v)))

/* Single-Copy Atomic 64-bit write with RELEASE memory ordering semantics*/
static inline void __sca_write64_release(uint64_t *ptr, uint64_t val)
{
	*ptr = val;
}
#define SCA_WRITE64_RELEASE(_p, _v) __sca_write64_release((uint64_t *)(_p), ((uint64_t)(_v)))

/* Return the 64-bit value at readable @ptr without modifying it. */
static inline uint64_t __sca_read64(const uint64_t *ptr)
{
	return *ptr;
}
#define SCA_READ64(_p) ((typeof(*(_p)))__sca_read64((const uint64_t *)(_p)))

/* Return the 64-bit value at readable @ptr for an emulated ACQUIRE read. */
static inline uint64_t __sca_read64_acquire(const uint64_t *ptr)
{
	return *ptr;
}
#define SCA_READ64_ACQUIRE(_p) ((typeof(*(_p)))__sca_read64_acquire((const uint64_t *)(_p)))

/* Single-Copy Atomic 32-bit write */
static inline void __sca_write32(uint32_t *ptr, uint32_t val)
{
	*ptr = val;
}
#define SCA_WRITE32(_p, _v) __sca_write32((uint32_t *)(_p), ((uint32_t)(_v)))

/* Single-Copy Atomic 32-bit write with RELEASE memory ordering semantics */
static inline void __sca_write32_release(uint32_t *ptr, uint32_t val)
{
	*ptr = val;
}
#define SCA_WRITE32_RELEASE(_p, _v) __sca_write32_release((uint32_t *)(_p), ((uint32_t)(_v)))

/* Return the 32-bit value at readable @ptr without modifying it. */
static inline uint32_t __sca_read32(const uint32_t *ptr)
{
	return *ptr;
}
#define SCA_READ32(_p) ((typeof(*(_p)))__sca_read32((const uint32_t *)(_p)))

/* Return the 32-bit value at readable @ptr for an emulated ACQUIRE read. */
static inline uint32_t __sca_read32_acquire(const uint32_t *ptr)
{
	return *ptr;
}
#define SCA_READ32_ACQUIRE(_p) ((typeof(*(_p)))__sca_read32_acquire((const uint32_t *)(_p)))

/* Return the 16-bit value at readable @ptr without modifying it. */
static inline uint16_t __sca_read16(const uint16_t *ptr)
{
	return *ptr;
}
#define SCA_READ16(_p) ((typeof(*(_p)))__sca_read16((const uint16_t *)(_p)))

/* Return the 16-bit value at readable @ptr for an emulated ACQUIRE read. */
static inline uint16_t __sca_read16_acquire(const uint16_t *ptr)
{
	return *ptr;
}
#define SCA_READ16_ACQUIRE(_p) ((typeof(*(_p)))__sca_read16_acquire((const uint16_t *)(_p)))

/* Return the byte at readable @ptr without modifying it. */
static inline uint8_t __sca_read8(const uint8_t *ptr)
{
	return *ptr;
}
#define SCA_READ8(_p) ((typeof(*(_p)))__sca_read8((const uint8_t *)(_p)))

/* Return the 8-bit value at readable @ptr for an emulated ACQUIRE read. */
static inline uint8_t __sca_read8_acquire(const uint8_t *ptr)
{
	return *ptr;
}
#define SCA_READ8_ACQUIRE(_p) ((typeof(*(_p)))__sca_read8_acquire((const uint8_t *)(_p)))

#endif /* MEMORY_H */

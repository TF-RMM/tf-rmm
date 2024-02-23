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

/* Single-Copy Atomic 64-bit read */
static inline uint64_t __sca_read64(uint64_t *ptr)
{
	return *ptr;
}
#define SCA_READ64(_p) ((typeof(*(_p)))__sca_read64((uint64_t *)(_p)))

/* Single-Copy Atomic 64-bit read with ACQUIRE memory ordering semantics */
static inline uint64_t __sca_read64_acquire(uint64_t *ptr)
{
	return *ptr;
}
#define SCA_READ64_ACQUIRE(_p) ((typeof(*(_p)))__sca_read64_acquire((uint64_t *)(_p)))

/* Single-Copy Atomic 16-bit read */
static inline uint16_t __sca_read16(uint16_t *ptr)
{
	return *ptr;
}
#define SCA_READ16(_p) ((typeof(*(_p)))__sca_read16((uint16_t *)(_p)))

/* Single-Copy Atomic 16-bit read with ACQUIRE memory ordering semantics */
static inline uint16_t __sca_read16_acquire(uint16_t *ptr)
{
	return *ptr;
}
#define SCA_READ16_ACQUIRE(_p) ((typeof(*(_p)))__sca_read16_acquire((uint16_t *)(_p)))


#endif /* MEMORY_H */

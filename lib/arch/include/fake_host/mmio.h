/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef MMIO_H
#define MMIO_H

#include <stdint.h>

static inline uint8_t read8(volatile void *addr)
{
	return *(uint8_t *)addr;
}

static inline void write8(uint8_t val, volatile void *addr)
{
	*(uint8_t *)addr = val;
}

static inline uint16_t read16(volatile void *addr)
{
	return *(uint16_t *)addr;
}

static inline void write16(uint16_t val, volatile void *addr)
{
	*(uint16_t *)addr = val;
}

static inline uint32_t read32(volatile void *addr)
{
	return *(uint32_t *)addr;
}

static inline void write32(uint32_t val, volatile void *addr)
{
	*(uint32_t *)addr = val;
}

static inline uint64_t read64(volatile void *addr)
{
	return *(uint64_t *)addr;
}

static inline void write64(uint64_t val, volatile void *addr)
{
	*(uint64_t *)addr = val;
}

#endif /* MMIO_H */

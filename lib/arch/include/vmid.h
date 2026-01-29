/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef VMID_H
#define VMID_H

#include <sizes.h>
#include <stdbool.h>

#define VMID8_COUNT		(U(1) << 8)
#define VMID16_COUNT		(U(1) << 16)
#define MAX_VMID_COUNT		VMID16_COUNT

/* The long int array size for VMID bitmap */
#define VMID_ARRAY_LONG_SIZE	(MAX_VMID_COUNT / BITS_PER_UL)

bool vmid_reserve(unsigned int vmid);
void vmid_free(unsigned int vmid);
void vmid_init(uintptr_t alloc, size_t alloc_size);

#endif /* VMID_H */

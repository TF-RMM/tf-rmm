/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TRACKING_REGION_ARCH_H
#define TRACKING_REGION_ARCH_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/*
 * Reservations are created during single-threaded initialization. Callers
 * must prevent concurrent changes to the page mappings they access.
 * CBMC models these operations without creating host mappings.
 */

/*
 * Reserve @size bytes of contiguous host VA and return the base in @va.
 * @size must be nonzero and granule aligned. Return 0 on success or -ENOMEM
 * if allocation fails or the reservation table is full. @va is valid only
 * on success.
 */
int tracking_region_arch_reserve(size_t size, uintptr_t *va);

/*
 * Alias backing at @pa into the reserved range [@va, @va + @size).
 * Both addresses and @size must be granule aligned, and the range must fit
 * within one reservation. Return 0 on success, -EINVAL for an invalid range
 * or -ENOMEM if the backing alias cannot be created.
 */
int tracking_region_arch_populate(uintptr_t va, uintptr_t pa, size_t size);

/*
 * Return the simulated PA corresponding to @va, including its page offset.
 * @va must lie within a reservation and its page must already be populated.
 */
uintptr_t tracking_region_arch_to_pa(uintptr_t va);

/* Return whether @va lies within a reservation and has a backing page. */
bool tracking_region_arch_is_mapped(uintptr_t va);

/*
 * Remove backing from [@va, @va + @size) while retaining the VA reservation.
 * @va and @size must be granule aligned, and the range must fit within one
 * reservation. Return 0 on success, -EINVAL for an invalid range or -ENOMEM
 * if the inaccessible mapping cannot be restored.
 */
int tracking_region_arch_depopulate(uintptr_t va, size_t size);

#endif /* TRACKING_REGION_ARCH_H */

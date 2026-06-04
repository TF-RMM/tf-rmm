/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef VDEV_TEST_H
#define VDEV_TEST_H

#include <dev.h>
#include <stdbool.h>
#include <stdint.h>

/*
 * Test-only wrappers that expose static PDEV vdev-range slot helpers so
 * unit tests can exercise multi-page slot storage without going through
 * the full device assignment object flows.
 *
 * Implemented in runtime/rmi/vdev.c.
 */
void vdev_test_pdev_set_vdev_ranges(struct pdev *pd, uint32_t slot_idx,
				    const struct rmi_address_range *addr_range,
				    unsigned long addr_range_cnt);
void vdev_test_pdev_clear_vdev_ranges(struct pdev *pd, uint32_t slot_idx);
bool vdev_test_pdev_vdev_range_slot_is_active(const struct pdev *pd,
					      uint32_t slot_idx);
uint32_t vdev_test_pdev_find_free_vdev_slot(const struct pdev *pd);
bool vdev_test_pdev_vdev_ranges_overlap(
	const struct pdev *pd,
	const struct rmi_address_range *addr_range,
	unsigned long addr_range_cnt);

#endif /* VDEV_TEST_H */

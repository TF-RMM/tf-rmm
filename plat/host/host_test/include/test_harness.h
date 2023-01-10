/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TEST_HARNESS_H
#define TEST_HARNESS_H

#include <buffer.h>

/*
 * Below functions are to be defined by the tests and allow them to implement
 * specific host harness APIs as defined in host_harness.h
 */

/*
 * Map a given granule address to a specific slot buffer
 * Args
 *	slot - Slot buffer type where to map to
 *	addr - Granule address to map
 * Return
 *	The VA (or platform equivalent) where the granule was mapped to
 */
void *test_buffer_map(enum buffer_slot slot, unsigned long addr);

/*
 * Unmap a given granule from its corresponding slot buffer given the
 * mapped granule address.
 */
void test_buffer_unmap(void *buf);

#endif /* TEST_HARNESS */

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SLOT_BUF_ARCH_H
#define SLOT_BUF_ARCH_H

#include <buffer.h>
#include <granule.h>
#include <granule_types.h>
#include <host_harness.h>

static void *buffer_arch_map(enum buffer_slot slot, unsigned long addr)
{
	return host_buffer_arch_map(slot, addr);
}

static void buffer_arch_unmap(void *buf)
{
	return host_buffer_arch_unmap(buf);
}

static void *buffer_arch_map_range(enum buffer_slot slot,
				   struct granule *g_arry[],
				   unsigned int slot_num)
{
	return host_buffer_arch_map(slot, granule_addr(g_arry[0]));
}

static void buffer_arch_unmap_range(void *buf, unsigned int num_slots)
{
	return host_buffer_arch_unmap(buf);
}

#endif /* SLOT_BUF_ARCH_H */

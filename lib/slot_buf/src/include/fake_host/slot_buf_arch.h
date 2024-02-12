/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SLOT_BUF_ARCH_H
#define SLOT_BUF_ARCH_H

#include <buffer.h>
#include <host_harness.h>

static void *buffer_arch_map(enum buffer_slot slot, unsigned long addr)
{
	return host_buffer_arch_map(slot, addr);
}

static void buffer_arch_unmap(void *buf)
{
	return host_buffer_arch_unmap(buf);
}

#endif /* SLOT_BUF_ARCH_H */

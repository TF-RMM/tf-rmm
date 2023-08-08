/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <xlat_tables.h>

struct xlat_llt_info *get_cached_llt_info(void);
uintptr_t slot_to_va(enum buffer_slot slot);
bool memcpy_ns_read(void *dest, const void *ns_src, size_t size);
bool memcpy_ns_write(void *ns_dest, const void *src, size_t size);

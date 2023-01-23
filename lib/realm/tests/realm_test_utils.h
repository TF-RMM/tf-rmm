/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef REALM_TEST_UTILS_H
#define REALM_TEST_UTILS_H

#include <buffer.h>

uintptr_t realm_test_util_slot_to_pa(enum buffer_slot slot);
uintptr_t realm_test_util_slot_va_from_pa(uintptr_t pa);
struct granule *realm_test_util_granule_struct_base(void);

#endif /* REALM_TEST_UTILS_H */

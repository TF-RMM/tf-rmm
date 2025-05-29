/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TEST_PRIVATE_H
#define TEST_PRIVATE_H

#include <test_helpers.h>

/*
 * Return a callback for a give callback ID
 */
uintptr_t get_cb(enum cb_ids id);

/* Implemented in init.c and needed in test_helpers.c */
uint64_t rmm_warmboot_main(void);
uint64_t rmm_main(void);

#endif /* TEST_PRIVATE_H */

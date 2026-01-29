/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* Stubs for CBMC analysis */

void mec_init_mmu(void)
{
	return;
}

void mec_init_state(uintptr_t state, size_t state_size)
{
    return;
}

unsigned int mecid_max(void)
{
    return 0;
}

int mec_set_private(unsigned int mecid)
{
    return 0;
}

int mec_set_shared(unsigned int mecid)
{
    return 0;
}

bool mecid_reserve(unsigned int mecid)
{
    return true;
}

void mecid_free(unsigned int mecid)
{
    /* No operation */
}

void _mecid_s1_get(unsigned int mecid)
{
    /* No operation */
}

void _mecid_s1_put(void)
{
    /* No operation */
}

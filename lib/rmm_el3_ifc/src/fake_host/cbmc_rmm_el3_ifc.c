/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <stdbool.h>
#include <tb_common.h>

void rmm_el3_ifc_report_fail_to_el3(int ec)
{
	ASSERT(false, "rmm_el3_ifc_report_fail_to_el3");
}

unsigned int rmm_el3_ifc_get_version(void)
{
	ASSERT(false, "rmm_el3_ifc_get_version");
	return 0;
}

uintptr_t rmm_el3_ifc_get_shared_buf_locked(void)
{
	ASSERT(false, "rmm_el3_ifc_get_shared_buf_locked");
	return 0;
}

void rmm_el3_ifc_release_shared_buf(void)
{
	ASSERT(false, "rmm_el3_ifc_release_shared_buf");
}

int rmm_el3_ifc_get_realm_attest_key(uintptr_t buf, size_t buflen,
				     size_t *len, unsigned int crv)
{
	ASSERT(false, "rmm_el3_ifc_get_realm_attest_key");
	return 0;
}

int rmm_el3_ifc_get_platform_token(uintptr_t buf, size_t buflen,
				   size_t hash_size,
				   size_t *token_hunk_len,
				   size_t *remaining_len)
{
	ASSERT(false, "rmm_el3_ifc_get_platform_token");
	return 0;
}

int rmm_el3_ifc_reserve_memory(size_t size, unsigned int flags,
			       unsigned long alignment, uintptr_t *address)
{
	ASSERT(false, "rmm_el3_ifc_reserve_memory");
	return 0;
}

int rmm_el3_ifc_init(unsigned long x0, unsigned long x1, unsigned long x2,
		     unsigned long x3, uintptr_t shared_buf_va)
{
	ASSERT(false, "rmm_el3_ifc_init");
	return 0;
}

#endif /* CBMC */

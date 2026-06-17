/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <firme.h>
#include <host_firme_ide_km.h>
#include <host_utils.h>

#ifndef CBMC
unsigned long host_firme_ide_keyset_prog(unsigned long ecam_addr,
					 unsigned long flags,
					 unsigned long keyset_id,
					 unsigned long kq_w0,
					 unsigned long kq_w1,
					 unsigned long kq_w2,
					 unsigned long kq_w3,
					 unsigned long handle)
{
	(void)ecam_addr;
	(void)flags;
	(void)keyset_id;
	(void)kq_w0;
	(void)kq_w1;
	(void)kq_w2;
	(void)kq_w3;
	(void)handle;

	INFO("Host EL3: firme_ide_prog: ecam/keyset/handle: 0x%lx/0x%lx/0x%lx\n",
	     ecam_addr, keyset_id, handle);

	return FIRME_SUCCESS;
}

unsigned long host_firme_ide_keyset_go(unsigned long ecam_addr,
				       unsigned long flags,
				       unsigned long keyset_id,
				       unsigned long handle)
{
	(void)ecam_addr;
	(void)flags;
	(void)keyset_id;
	(void)handle;

	INFO("Host EL3: firme_ide_go: ecam/keyset/handle: 0x%lx/0x%lx/0x%lx\n",
	     ecam_addr, keyset_id, handle);

	return FIRME_SUCCESS;
}

unsigned long host_firme_ide_keyset_stop(unsigned long ecam_addr,
					 unsigned long flags,
					 unsigned long keyset_id,
					 unsigned long handle)
{
	(void)ecam_addr;
	(void)flags;
	(void)keyset_id;
	(void)handle;

	INFO("Host EL3: firme_ide_stop: ecam/keyset/handle: 0x%lx/0x%lx/0x%lx\n",
	     ecam_addr, keyset_id, handle);

	return FIRME_SUCCESS;
}
#endif /* CBMC */

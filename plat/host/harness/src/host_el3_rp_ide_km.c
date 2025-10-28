/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <host_el3_rp_ide_km.h>
#include <host_utils.h>
#include <rmm_el3_ifc.h>

#ifndef CBMC
unsigned long host_el3_rp_ide_key_prog(unsigned long ecam_addr,
				       unsigned long rp_id,
				       unsigned long stream_info,
				       unsigned long kq_w0, unsigned long kq_w1,
				       unsigned long kq_w2, unsigned long kq_w3,
				       unsigned long iv_w0, unsigned long iv_w1)
{
	(void)ecam_addr;
	(void)rp_id;
	(void)stream_info;
	(void)kq_w0;
	(void)kq_w1;
	(void)kq_w2;
	(void)kq_w3;
	(void)iv_w0;
	(void)iv_w1;

	INFO("Host EL3: rp_ide_key_prog: ecam/RP/sinfo: 0x%lx/0x%lx/0x%lx\n",
	     ecam_addr, rp_id, stream_info);

	return E_RMM_OK;
}

unsigned long host_el3_rp_ide_key_set_go(unsigned long ecam_addr,
					 unsigned long rp_id,
					 unsigned long stream_info)
{
	(void)ecam_addr;
	(void)rp_id;
	(void)stream_info;

	INFO("Host EL3: rp_ide_key_set_go: ecam/RP/sinfo: 0x%lx/0x%lx/0x%lx\n",
	     ecam_addr, rp_id, stream_info);

	return E_RMM_OK;
}

unsigned long host_el3_rp_ide_key_set_stop(unsigned long ecam_addr,
					   unsigned long rp_id,
					   unsigned long stream_info)
{
	(void)ecam_addr;
	(void)rp_id;
	(void)stream_info;

	INFO("Host EL3: rp_ide_key_set_stop: ecam/RP/sinfo: 0x%lx/0x%lx/0x%lx\n",
	     ecam_addr, rp_id, stream_info);

	return E_RMM_OK;
}
#endif /* CBMC */

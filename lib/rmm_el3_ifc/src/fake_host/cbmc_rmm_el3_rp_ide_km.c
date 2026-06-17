/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <rmm_el3_ifc.h>
#include <stdbool.h>
#include <tb_common.h>

int rmm_el3_ifc_rp_ide_key_prog(unsigned long ecam_addr, unsigned long rp_id,
				unsigned long kslot, unsigned long kdir,
				unsigned long ide_sub_sid,
				unsigned long ide_sid,
				struct el3_ifc_rp_ide_key *key,
				struct el3_ifc_rp_ide_iv *iv)
{
	ASSERT(false, "rmm_el3_ifc_rp_ide_key_prog");
	return 0;
}

int rmm_el3_ifc_rp_ide_key_set_go(unsigned long ecam_addr, unsigned long rp_id,
				  unsigned long kslot, unsigned long kdir,
				  unsigned long ide_sub_sid,
				  unsigned long ide_sid)
{
	ASSERT(false, "rmm_el3_ifc_rp_ide_key_set_go");
	return 0;
}

int rmm_el3_ifc_rp_ide_key_set_stop(unsigned long ecam_addr, unsigned long rp_id,
				    unsigned long kslot, unsigned long kdir,
				    unsigned long ide_sub_sid,
				    unsigned long ide_sid)
{
	ASSERT(false, "rmm_el3_ifc_rp_ide_key_set_stop");
	return 0;
}

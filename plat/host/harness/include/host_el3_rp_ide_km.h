/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_EL3_RP_IDE_KM_H
#define HOST_EL3_RP_IDE_KM_H

#include <stddef.h>
#include <types.h>

unsigned long host_el3_rp_ide_key_prog(unsigned long ecam_addr,
				       unsigned long rp_id,
				       unsigned long stream_info,
				       unsigned long kq_w0, unsigned long kq_w1,
				       unsigned long kq_w2, unsigned long kq_w3,
				       unsigned long iv_w0, unsigned long iv_w1);

unsigned long host_el3_rp_ide_key_set_go(unsigned long ecam_addr,
					 unsigned long rp_id,
					 unsigned long stream_info);

unsigned long host_el3_rp_ide_key_set_stop(unsigned long ecam_addr,
					   unsigned long rp_id,
					   unsigned long stream_info);

#endif /* HOST_EL3_RP_IDE_KM_H */

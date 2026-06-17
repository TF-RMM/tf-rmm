/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_FIRME_IDE_KM_H
#define HOST_FIRME_IDE_KM_H

#include <stddef.h>
#include <types.h>

unsigned long host_firme_ide_keyset_prog(unsigned long ecam_addr,
					 unsigned long flags,
					 unsigned long keyset_id,
					 unsigned long kq_w0,
					 unsigned long kq_w1,
					 unsigned long kq_w2,
					 unsigned long kq_w3,
					 unsigned long handle);

unsigned long host_firme_ide_keyset_go(unsigned long ecam_addr,
				       unsigned long flags,
				       unsigned long keyset_id,
				       unsigned long handle);

unsigned long host_firme_ide_keyset_stop(unsigned long ecam_addr,
					 unsigned long flags,
					 unsigned long keyset_id,
					 unsigned long handle);
#endif /* HOST_FIRME_IDE_KM_H */

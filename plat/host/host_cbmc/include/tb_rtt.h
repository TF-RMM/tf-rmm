/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TB_RTT_H
#define TB_RTT_H

bool valid_num_root_rtts(unsigned int num_root_rtts);
struct granule *init_rtt_root_page(unsigned int num_root_rtts);

#endif

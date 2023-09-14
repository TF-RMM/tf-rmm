/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RSI_WALK_H
#define RSI_WALK_H

#include <stdbool.h>

struct rsi_walk_result {
	/*
	 * If true, RTT walk failed due to missing PTE at level @rtt_level.
	 */
	bool abort;

	/*
	 * RTT level at which the walk terminated.
	 */
	unsigned long rtt_level;
};

#endif /* RSI_WALK_H */

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RSI_WALK_H
#define RSI_WALK_H

struct rsi_walk_result {
	/*
	 * If true, RTT walk failed due to missing PTE at level @rtt_level.
	 *
	 * If false, @smc_result contains GPR values to be returned to the
	 * Realm.
	 */
	bool abort;
	unsigned long rtt_level;
};

#endif /* RSI_WALK_H */

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef __ACTIVATE__
#define __ACTIVATE__

/*
 * Possible states of the RMM. Note that some SMCs can only be
 * dispatched when state is RMM_STATE_ACTIVE.
 */
enum rmm_state {
	RMM_STATE_INIT,
	RMM_STATE_INTERMEDIATE,
	RMM_STATE_ACTIVE
};

/* Return the activation state of RMM */
enum rmm_state get_rmm_active_state(void);

#endif /* __ACTIVATE__ */

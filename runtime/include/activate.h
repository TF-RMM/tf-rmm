/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef __ACTIVATE__
#define __ACTIVATE__

#include <smc-rmi.h>

/* Return a synchronized snapshot of the global RMM lifecycle state. */
enum rmm_state get_rmm_active_state(void);

#endif /* __ACTIVATE__ */

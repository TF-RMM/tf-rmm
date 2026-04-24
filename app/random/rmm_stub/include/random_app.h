/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RANDOM_APP_H
#define RANDOM_APP_H

#include <app.h>
#include <stddef.h>

void random_app_init_prng(void);
struct app_data_cfg *random_app_get_data_cfg(void);
int random_app_prng_get_random(struct app_data_cfg *app_data, uint8_t *buf, size_t output_size);

/*
 * ONLY FOR TESTING PURPOSES.
 * Reset all per-cpu random app instance state. Must be called after
 * app_processes_cleanup() to prevent stale FDs/thread IDs being used.
 */
void random_reset_app_state(void);

#endif /* RANDOM_APP_H */

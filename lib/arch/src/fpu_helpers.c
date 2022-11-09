/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <cpuid.h>
#include <fpu_helpers.h>
#include <stdbool.h>

struct rmm_fpu_state {
	struct fpu_state state;
	bool saved;
};

struct rmm_fpu_state rmm_fpu_state[MAX_CPUS];

#ifdef RMM_FPU_USE_AT_REL2
void fpu_save_my_state(void)
{
	struct rmm_fpu_state *rmm_state;
	unsigned int cpu_id = my_cpuid();

	rmm_state = rmm_fpu_state + cpu_id;
	assert(!rmm_state->saved);
	rmm_state->saved = true;
	FPU_ALLOW(fpu_save_state(&(rmm_state->state)));
}

void fpu_restore_my_state(void)
{
	struct rmm_fpu_state *rmm_state;
	unsigned int cpu_id = my_cpuid();

	rmm_state = rmm_fpu_state + cpu_id;
	assert(rmm_state->saved);
	FPU_ALLOW(fpu_restore_state(&(rmm_state->state)));
	rmm_state->saved = false;
}

bool fpu_is_my_state_saved(unsigned int cpu_id)
{
	assert(cpu_id < MAX_CPUS);
	return rmm_fpu_state[cpu_id].saved;
}

#else /* RMM_FPU_USE_AT_REL2 */
void fpu_save_my_state(void) {}

void fpu_restore_my_state(void) {}

#endif /* RMM_FPU_USE_AT_REL2 */

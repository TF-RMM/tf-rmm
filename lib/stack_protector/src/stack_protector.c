/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <cpuid.h>
#include <debug.h>
#include <entropy.h>
#include <spinlock.h>
#include <stack_protector.h>
#include <types.h>
#include <utils_def.h>

static spinlock_t stack_canary_init_lock = {0U};

static bool stack_init;

/* __stack_chk_guard and __stack_chk_fail is only used in AArch64.
 *
 * NOT used in fake host because there are already protection mechanisms
 * which interfere with this mechanism.
 */

/*
 * Canary value used by the compiler runtime checks to detect stack corruption.
 */
/* cppcheck-suppress [misra-c2012-8.4] */
/* coverity[misra_c_2012_rule_8_4_violation:SUPPRESS] */
u_register_t __stack_chk_guard = (u_register_t) 1;

/*
 * Function called when the stack canary check fails.
 * It must not return and the program will stop.
 */
void __dead2 __stack_chk_fail(void)
{
	ERROR("Stack corruption detected\n");
	panic();
}

/*
 * Function is used to initialize/update canary value.
 * no_stack protector attribute needs to be specified
 * for this function.
 */
__attribute__((no_stack_protector))
void rmm_init_stack_canary(void)
{
	spinlock_acquire(&stack_canary_init_lock);

	/* If initialized already, then skip*/
	if (stack_init) {
		spinlock_release(&stack_canary_init_lock);
		return;
	}

	while (!(arch_collect_entropy(&__stack_chk_guard))) {
	}

	stack_init = true;

	spinlock_release(&stack_canary_init_lock);
}

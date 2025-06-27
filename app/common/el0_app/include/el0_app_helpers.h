/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef EL0_APP_HELPERS_H
#define EL0_APP_HELPERS_H

#include <el0_app_helpers_arch.h>
#include <stddef.h>

void *get_shared_mem_start(void);
size_t get_shared_mem_size(void);

/*
 * This function must be defined by the app that uses Mbed TLS allocator
 *
 * The function returns the start address to a buffer_alloc_ctx object.
 */
/* coverity[misra_c_2012_rule_5_8_violation:SUPPRESS] */
void *mbedtls_app_get_heap(void);

/* coverity[misra_c_2012_rule_5_8_violation:SUPPRESS] */
unsigned long el0_app_entry_func(
	unsigned long func_id,
	unsigned long arg_0,
	unsigned long arg_1,
	unsigned long arg_2,
	unsigned long arg_3);

unsigned long el0_app_service_call(unsigned long service_index,
				   unsigned long arg0,
				   unsigned long arg1,
				   unsigned long arg2,
				   unsigned long arg3);

void el0_app_yield(void);

#endif /* EL0_APP_HELPERS_H */


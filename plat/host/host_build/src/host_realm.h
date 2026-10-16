/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_REALM_H
#define HOST_REALM_H

#include <host_da.h>
#include <minicoro.h>
#include <smc-rmi.h>

#define REALM_BUFFER_IPA		0x1000
#define REALM_BUFFER_IPA_1		0x1000
#define REALM_BUFFER_IPA_2		0x10000

#define CHECK_RMI_RESULT() \
({  \
	if (result.x[0] != RMI_SUCCESS) {				\
		ERROR("RMI call failed at %s:%d. status=%lu.\n",	\
			__FILE__, __LINE__, result.x[0]);		\
		return -1;						\
	}								\
})

uint64_t rmm_main(void);
int realm_start(unsigned long *regs, unsigned long *rec_sp_el0);
unsigned long host_realm_get_realm_data_1(void);
void print_buf(const unsigned char *buf, size_t size);

/* Shared realm coroutine state */
extern unsigned long *g_rec_regs;
extern int g_realm_ret;

void realm_rsi_call(mco_coro *co);
void realm_da_rsi_coro(mco_coro *co);

unsigned long host_realm_get_realm_buffer(void);

#endif /* HOST_REALM_H */

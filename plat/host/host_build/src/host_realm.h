/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_REALM_H
#define HOST_REALM_H

#include <smc-rmi.h>

/* Create a simple 4 level (Lvl 0 - LvL 3) RTT structure */
#define RTT_COUNT 4

#define REALM_BUFFER_IPA		0x1000

#define CHECK_RMI_RESULT() \
({  \
	if (result.x[0] != RMI_SUCCESS) {				\
		ERROR("RMI call failed at %s:%d. status=%lu.\n",	\
			__FILE__, __LINE__, result.x[0]);		\
		return -1;						\
	}								\
})

struct host_realm {
	void *rd;
	void *rec;
	unsigned long rec_aux_count;
	void *rtts[RTT_COUNT];
	void *rec_aux_granules[MAX_REC_AUX_GRANULES];
	struct rmi_realm_params *realm_params;
	struct rmi_rec_params *rec_params;
	struct rmi_rec_run *rec_run;
	uintptr_t realm_buffer;
};

uint64_t rmm_main(uint64_t token);
int realm_start(unsigned long *regs, unsigned long *rec_sp_el0);

unsigned long host_realm_get_realm_buffer(void);

#endif /* HOST_REALM_H */

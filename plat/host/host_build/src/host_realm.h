/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_REALM_H
#define HOST_REALM_H

#include <minicoro.h>
#include <smc-rmi.h>

/* Create a simple 4 level (Lvl 0 - LvL 3) RTT structure */
#define RTT_COUNT 4

#define REALM_BUFFER_IPA		0x1000
#define HOST_DA_VDEV_ID			0U
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

struct host_realm {
	void *rd;
	void *rec;
	void *rtts[RTT_COUNT];
	struct rmi_realm_params *realm_params;
	struct rmi_rec_params *rec_params;
	struct rmi_rec_run *rec_run;
	uintptr_t realm_data_1;
	size_t realm_data_1_num_gr;
	uintptr_t realm_data_2;
	size_t realm_data_2_num_gr;
};

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
int host_sro_drive(unsigned long handle, unsigned long ret_status,
		   unsigned long donate_req);
int host_pdev_probe_and_setup(void);
int host_psmmu_setup(unsigned int smmu_idx, unsigned long sid);
int host_vdev_assign(struct host_realm *realm, unsigned long host_vdev_tdi_id);
int host_realm_run_da(struct host_realm *realm);
int host_pdev_reclaim(int host_pdev_id);
int host_vdev_reclaim(struct host_realm *realm, int host_vdev_id);

#endif /* HOST_REALM_H */

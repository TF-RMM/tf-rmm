/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <host_realm.h>
#include <host_rmi_wrappers.h>
#include <host_utils.h>
#define MINICORO_IMPL
#include <minicoro.h>
#include <smc-rsi.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <utils_def.h>

#define ATTEST_TOKEN_BUFFER_SIZE	0x100
#define REALM_BUFFER_IPA		0x1000  /* This has to match a valid IPA in host_setup.c */

/* Shared state between realm_start and realm coroutines */
unsigned long *g_rec_regs;
int g_realm_ret;

void print_buf(const unsigned char *buf, size_t size)
{
	size_t i;

	assert(buf != NULL);

	for (i = 0; i < size; ++i) {
		if ((i & 0xF) == 0) {
			VERBOSE("\n");
		}
		VERBOSE(" %02x", buf[i]);
	}
	VERBOSE("\n\n");
}

/*
 * Yield from realm coroutine to issue an RSI call.
 * Sets up the RSI command in rec_regs before yielding.
 * On resume, rec_regs contains the RSI response.
 */
void realm_rsi_call(mco_coro *co)
{
	g_realm_ret = ARM_EXCEPTION_SYNC_LEL;
	mco_yield(co);
}

/*
 * Realm attestation coroutine.
 * Each realm_rsi_call() yields to the host which processes the RSI
 * via RMI_REC_ENTER. On resume, g_rec_regs has the RSI response.
 */
static void realm_attest_coro(mco_coro *co)
{
	unsigned long offset;
	size_t token_size;

	INFO("###########################\n");
	INFO("# Hello World from a Realm!\n");
	INFO("###########################\n");

	/* RSI_VERSION */
	g_rec_regs[0] = SMC_RSI_VERSION;
	g_rec_regs[1] = MAKE_RSI_REVISION(1, 0);
	realm_rsi_call(co);

	INFO("RSI Version is 0x%lx : 0x%lx\n", g_rec_regs[1], g_rec_regs[2]);
	if (g_rec_regs[0] != RSI_SUCCESS) {
		ERROR("RSI_VERSION command failed 0x%lx\n", g_rec_regs[0]);
		g_realm_ret = ARM_EXCEPTION_SYNC_LEL;
		return;
	}

	srand((int)time(NULL));

	/* RSI_ATTEST_TOKEN_INIT */
	g_rec_regs[0] = SMC_RSI_ATTEST_TOKEN_INIT;
	g_rec_regs[1] = rand();
	g_rec_regs[2] = rand();
	g_rec_regs[3] = rand();
	g_rec_regs[4] = rand();
	g_rec_regs[5] = rand();
	g_rec_regs[6] = rand();
	g_rec_regs[7] = rand();
	g_rec_regs[8] = rand();
	realm_rsi_call(co);

	if (g_rec_regs[0] != RSI_SUCCESS) {
		ERROR("Realm token initialization failed 0x%lx\n", g_rec_regs[0]);
		g_realm_ret = ARM_EXCEPTION_SYNC_LEL;
		return;
	}

	INFO("Upper bound of attestation token size: 0x%lx\n", g_rec_regs[1]);
	assert(g_rec_regs[1] >= ATTEST_TOKEN_BUFFER_SIZE);

	/* Pend an IRQ and invoke the RSI which should cause an exit to NS */
	host_write_sysreg("isr_el1", 0x80);

	/* RSI_ATTEST_TOKEN_CONTINUE loop */
	offset = 0;
	g_rec_regs[0] = SMC_RSI_ATTEST_TOKEN_CONTINUE;
	g_rec_regs[1] = REALM_BUFFER_IPA;
	g_rec_regs[2] = 0;
	g_rec_regs[3] = ATTEST_TOKEN_BUFFER_SIZE;
	realm_rsi_call(co);

	while (g_rec_regs[0] == RSI_INCOMPLETE) {
		INFO("Realm Token Attestation creation is pre-empted by interrupt.\n");
		offset += g_rec_regs[1];

		g_rec_regs[0] = SMC_RSI_ATTEST_TOKEN_CONTINUE;
		g_rec_regs[1] = REALM_BUFFER_IPA;
		g_rec_regs[2] = offset;
		g_rec_regs[3] = ATTEST_TOKEN_BUFFER_SIZE;
		realm_rsi_call(co);
	}

	if (g_rec_regs[0] != RSI_SUCCESS) {
		ERROR("Realm Token Attestation continue failed\n");
		g_realm_ret = ARM_EXCEPTION_SYNC_LEL;
		return;
	}

	token_size = offset + g_rec_regs[1];
	VERBOSE("Print attestation token (size: %ld):\n", token_size);

	print_buf((const unsigned char *)host_realm_get_realm_data_1(),
		  token_size);

	g_realm_ret = ARM_EXCEPTION_FIQ_LEL;
}

static mco_coro *g_realm_coro;

typedef void (*realm_coro_fn)(mco_coro *);

static realm_coro_fn g_realm_coro_list[] = {
	realm_attest_coro,
	realm_da_rsi_coro,
};

static unsigned int g_coro_index;

int realm_start(unsigned long *regs, unsigned long *rec_sp_el0)
{
	(void)rec_sp_el0;

	g_rec_regs = regs;

	while (g_coro_index < ARRAY_SIZE(g_realm_coro_list)) {
		if (g_realm_coro == NULL) {
			mco_desc desc = mco_desc_init(
					g_realm_coro_list[g_coro_index], 0);
			mco_result res __unused =
					mco_create(&g_realm_coro, &desc);

			assert(res == MCO_SUCCESS);
		}

		mco_resume(g_realm_coro);

		if (mco_status(g_realm_coro) == MCO_DEAD) {
			mco_destroy(g_realm_coro);
			g_realm_coro = NULL;
			g_coro_index++;
			/*
			 * Return to the host so it can process the exit
			 * (e.g. FIQ from attestation). The next coroutine
			 * will start on the subsequent rec_enter.
			 */
			return g_realm_ret;
		} else {
			/*
			 * Coroutine yielded for an RSI call.
			 * Set ELR_EL2 back to realm_start so we
			 * re-enter here.
			 */
			write_elr_el2((u_register_t)realm_start - 0x4);
			write_esr_el2(ESR_EL2_EC_SMC);
			return g_realm_ret;
		}
	}

	return g_realm_ret;
}

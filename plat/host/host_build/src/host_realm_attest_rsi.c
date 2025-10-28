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
#include <smc-rsi.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define ATTEST_TOKEN_BUFFER_SIZE	0x100
#define REALM_BUFFER_IPA		0x1000

static void print_buf(const unsigned char *buf, size_t size)
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

static int realm_continue_2(unsigned long *rec_regs, unsigned long *rec_sp_el0)
{
	(void)rec_sp_el0;

	static unsigned long offset;
	size_t token_size;

	if (rec_regs[0] == RSI_INCOMPLETE) {
		INFO("Realm Token Attestation creation is pre-empted by interrupt.\n");

		offset += rec_regs[1];

		/* Continue Realm Attestation RSI calls */
		rec_regs[0] = SMC_RSI_ATTEST_TOKEN_CONTINUE;
		rec_regs[1] = REALM_BUFFER_IPA;
		rec_regs[2] = offset;
		rec_regs[3] = ATTEST_TOKEN_BUFFER_SIZE;
		return host_util_rsi_helper(realm_continue_2);
	}

	if (rec_regs[0] != RSI_SUCCESS) {
		ERROR("Realm Token Attestation continue failed\n");
		return 0;
	}

	token_size = offset + rec_regs[1];

	VERBOSE("Print attestation token (size: %ld):\n", token_size);

	/*
	 * As the realm buffer is allocated by host_setup, use a helper to get
	 * the realm buffer address that is delegated to the Realm
	 */
	print_buf((const unsigned char *)host_realm_get_realm_buffer(),
		  token_size);

	/* Simulate return back to NS due to FIQ */
	return ARM_EXCEPTION_FIQ_LEL;
}

static int realm_continue_1(unsigned long *rec_regs, unsigned long *rec_sp_el0)
{
	(void)rec_sp_el0;

	if (rec_regs[0] != RSI_SUCCESS) {
		ERROR("Realm token initialization failed 0x%lx\n", rec_regs[0]);
		return 0;
	}

	INFO("Upper bound of attestation token size: 0x%lx\n", rec_regs[1]);
	assert(rec_regs[1] >= ATTEST_TOKEN_BUFFER_SIZE);

	/* Pend an IRQ and invoke the RSI which should cause an exit to NS */
	host_write_sysreg("isr_el1", 0x80);

	/* Continue Realm Attestation RSI calls */
	rec_regs[0] = SMC_RSI_ATTEST_TOKEN_CONTINUE;
	rec_regs[1] = REALM_BUFFER_IPA;
	rec_regs[2] = 0;
	rec_regs[3] = ATTEST_TOKEN_BUFFER_SIZE;
	return host_util_rsi_helper(realm_continue_2);
}

static int realm_continue(unsigned long *rec_regs, unsigned long *rec_sp_el0)
{
	(void)rec_sp_el0;

	INFO("RSI Version is 0x%lx : 0x%lx\n", rec_regs[1], rec_regs[2]);

	if (rec_regs[0] != RSI_SUCCESS) {
		ERROR("RSI_VERSION command failed 0x%lx\n", rec_regs[0]);
		return 0;
	}

	srand((int)time(NULL));

	/* Add dummy Realm Attestation RSI calls */
	rec_regs[0] = SMC_RSI_ATTEST_TOKEN_INIT;
	rec_regs[1] = rand();
	rec_regs[2] = rand();
	rec_regs[3] = rand();
	rec_regs[4] = rand();
	rec_regs[5] = rand();
	rec_regs[6] = rand();
	rec_regs[7] = rand();
	rec_regs[8] = rand();

	return host_util_rsi_helper(realm_continue_1);
}

int realm_start(unsigned long *regs)
{
	INFO("###########################\n");
	INFO("# Hello World from a Realm!\n");
	INFO("###########################\n");

	regs[0] = SMC_RSI_VERSION;
	regs[1] = MAKE_RSI_REVISION(1, 0);
	return host_util_rsi_helper(realm_continue);
}

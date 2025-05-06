/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_header.h>
#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <host_rmi_wrappers.h>
#include <host_utils.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <s2tt.h>
#include <smc-rmi.h>
#include <smc-rsi.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Create a simple 4 level (Lvl 0 - LvL 3) RTT structure */
#define RTT_COUNT 4

/* Define the EL3-RMM interface version as set from EL3 */
#define EL3_IFC_ABI_VERSION		\
	RMM_EL3_IFC_MAKE_VERSION(RMM_EL3_IFC_VERS_MAJOR, 4)
#define RMM_EL3_MAX_CPUS		(1U)
#define REALM_BUFFER_IPA		0x1000
#define ATTEST_TOKEN_BUFFER_SIZE	0x100

#define CHECK_RMI_RESULT() \
({  \
	if (result.x[0] != RMI_SUCCESS) {				\
		ERROR("RMI call failed at %s:%d. status=%lu.\n",	\
			__FILE__, __LINE__, result.x[0]);		\
		return -1;						\
	}								\
})

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

/*
 * Function to emulate the MMU enablement for the fake_host architecture.
 */
static void enable_fake_host_mmu(void)
{
	write_sctlr_el2(SCTLR_ELx_WXN_BIT | SCTLR_ELx_M_BIT);
}

static void *allocate_granule(void)
{
	static unsigned int next_granule_index;
	unsigned long granule;

	if (next_granule_index >= HOST_NR_GRANULES) {
		panic();
	}

	granule = host_util_get_granule_base() +
		  next_granule_index * GRANULE_SIZE;
	++next_granule_index;

	return (void *)granule;
}

static int realm_continue(unsigned long *regs);
static int realm_continue_1(unsigned long *regs);
static int realm_continue_2(unsigned long *regs);

uintptr_t realm_buffer;
static size_t token_size;

static int realm_start(unsigned long *regs)
{
	INFO("###########################\n");
	INFO("# Hello World from a Realm!\n");
	INFO("###########################\n");

	regs[0] = SMC_RSI_VERSION;
	regs[1] = MAKE_RSI_REVISION(1, 0);
	return host_util_rsi_helper(realm_continue);
}

static int realm_continue(unsigned long *regs)
{
	INFO("RSI Version is 0x%lx : 0x%lx\n", regs[1], regs[2]);

	if (regs[0] != RSI_SUCCESS) {
		ERROR("RSI_VERSION command failed 0x%lx\n", regs[0]);
		return 0;
	}

	srand((int)time(NULL));

	/* Add dummy Realm Attestation RSI calls */
	regs[0] = SMC_RSI_ATTEST_TOKEN_INIT;
	regs[1] = rand();
	regs[2] = rand();
	regs[3] = rand();
	regs[4] = rand();
	regs[5] = rand();
	regs[6] = rand();
	regs[7] = rand();
	regs[8] = rand();

	return host_util_rsi_helper(realm_continue_1);
}

static int realm_continue_1(unsigned long *regs)
{
	if (regs[0] != RSI_SUCCESS) {
		ERROR("Realm token initialization failed 0x%lx\n", regs[0]);
		return 0;
	}

	INFO("Upper bound of attestation token size: 0x%lx\n", regs[1]);
	assert(regs[1] >= ATTEST_TOKEN_BUFFER_SIZE);

	/* Pend an IRQ and invoke the RSI which should cause an exit to NS */
	host_write_sysreg("isr_el1", 0x80);

	/* Continue Realm Attestation RSI calls */
	regs[0] = SMC_RSI_ATTEST_TOKEN_CONTINUE;
	regs[1] = REALM_BUFFER_IPA;
	regs[2] = 0;
	regs[3] = ATTEST_TOKEN_BUFFER_SIZE;
	return host_util_rsi_helper(realm_continue_2);
}

static int realm_continue_2(unsigned long *regs)
{
	static unsigned long offset;

	if (regs[0] == RSI_INCOMPLETE) {
		INFO("Realm Token Attestation creation is pre-empted by interrupt.\n");

		offset += regs[1];

		/* Continue Realm Attestation RSI calls */
		regs[0] = SMC_RSI_ATTEST_TOKEN_CONTINUE;
		regs[1] = REALM_BUFFER_IPA;
		regs[2] = offset;
		regs[3] = ATTEST_TOKEN_BUFFER_SIZE;
		return host_util_rsi_helper(realm_continue_2);
	}

	if (regs[0] != RSI_SUCCESS) {
		ERROR("Realm Token Attestation continue failed\n");
		return 0;
	}

	token_size = offset + regs[1];

	/* Simulate return back to NS due to FIQ */
	return ARM_EXCEPTION_FIQ_LEL;
}

static int create_realm(void)
{
	struct smc_result result;
	unsigned long rec_aux_count;
	unsigned int i;
	void *rtts[RTT_COUNT];
	void *rec_aux_granules[MAX_REC_AUX_GRANULES];
	void *rd = allocate_granule();
	void *rec = allocate_granule();
	struct rmi_realm_params *realm_params = allocate_granule();
	struct rmi_rec_params *rec_params = allocate_granule();
	struct rmi_rec_run *rec_run = allocate_granule();

	host_rmi_version(MAKE_RMI_REVISION(1, 0), &result);
	CHECK_RMI_RESULT();
	INFO("RMI Version is 0x%lx : 0x%lx\n", result.x[1], result.x[2]);

	host_rmi_granule_delegate(rd, &result);
	CHECK_RMI_RESULT();
	host_rmi_granule_delegate(rec, &result);
	CHECK_RMI_RESULT();
	for (i = 0; i < RTT_COUNT; ++i) {
		rtts[i] = allocate_granule();
		host_rmi_granule_delegate(rtts[i], &result);
		CHECK_RMI_RESULT();
	}

	memset(realm_params, 0, sizeof(*realm_params));
	realm_params->s2sz = arch_feat_get_pa_width();
	realm_params->rtt_num_start = 1;
	realm_params->rtt_base = (uintptr_t)rtts[0];
	realm_params->num_bps = 1;
	realm_params->num_wps = 1;

	host_rmi_realm_create(rd, realm_params, &result);
	CHECK_RMI_RESULT();

	/* Create RTT table to start at IPA 0x0 */
	for (i = 1; i < RTT_COUNT; ++i) {
		host_rmi_rtt_create(rd, rtts[i], 0, i, &result);
		CHECK_RMI_RESULT();
	}

	realm_buffer = (uintptr_t)allocate_granule();
	host_rmi_granule_delegate((void *)realm_buffer, &result);
	CHECK_RMI_RESULT();

	host_rmi_rtt_init_ripas(rd, REALM_BUFFER_IPA,
				REALM_BUFFER_IPA + GRANULE_SIZE,
				&result);
	CHECK_RMI_RESULT();

	host_rmi_data_create_unknown(rd, realm_buffer, REALM_BUFFER_IPA, &result);
	CHECK_RMI_RESULT();

	host_rmi_rec_aux_count(rd, &result);
	CHECK_RMI_RESULT();
	rec_aux_count = result.x[1];

	assert(rec_aux_count == MAX_REC_AUX_GRANULES);
	INFO("A rec requires %lu rec aux pages\n", rec_aux_count);

	memset(rec_params, 0, sizeof(*rec_params));
	for (i = 0; i < rec_aux_count; ++i) {
		rec_aux_granules[i] = allocate_granule();
		rec_params->aux[i] = (uintptr_t)rec_aux_granules[i];
		host_rmi_granule_delegate(rec_aux_granules[i], &result);
		CHECK_RMI_RESULT();
	}
	rec_params->num_aux = rec_aux_count;
	rec_params->flags |= REC_PARAMS_FLAG_RUNNABLE;
	rec_params->pc = (uintptr_t)realm_start;

	host_rmi_rec_create(rd, rec, rec_params, &result);
	CHECK_RMI_RESULT();
	host_rmi_realm_activate(rd, &result);
	CHECK_RMI_RESULT();

	/* Execute the Realm */
	memset(rec_run, 0, sizeof(*rec_run));
	host_rmi_rec_enter(rec, rec_run, &result);
	CHECK_RMI_RESULT();

	while (rec_run->exit.exit_reason == RMI_EXIT_IRQ) {
		/* Clear the IRQ in ISR_EL1 and re-enter Realm */
		host_write_sysreg("isr_el1", 0x0);
		host_rmi_rec_enter(rec, rec_run, &result);
		CHECK_RMI_RESULT();
	}

	if (rec_run->exit.exit_reason == RMI_EXIT_FIQ) {
		INFO("Realm executed successfully and exited due to FIQ.\n");
	}

	VERBOSE("Print attestation token (size: %ld):\n", token_size);
	print_buf((void *)realm_buffer, token_size);

	host_rmi_rec_destroy(rec, &result);
	CHECK_RMI_RESULT();

	for (i = 0; i < rec_aux_count; ++i) {
		host_rmi_granule_undelegate(rec_aux_granules[i], &result);
		CHECK_RMI_RESULT();
	}

	host_rmi_data_destroy(rd, REALM_BUFFER_IPA, &result);
	CHECK_RMI_RESULT();
	host_rmi_granule_undelegate((void *)realm_buffer, &result);
	CHECK_RMI_RESULT();

	for (i = RTT_COUNT-1; i >= 1; --i) {
		host_rmi_rtt_destroy(rd, 0, i, &result);
		CHECK_RMI_RESULT();
		host_rmi_granule_undelegate(rtts[i], &result);
		CHECK_RMI_RESULT();
	}

	host_rmi_realm_destroy(rd, &result);
	CHECK_RMI_RESULT();
	host_rmi_granule_undelegate(rd, &result);
	CHECK_RMI_RESULT();
	host_rmi_granule_undelegate(rec, &result);
	CHECK_RMI_RESULT();
	return 0;
}

void rmm_main(void);

void print_help(char *app_name)
{
	rmm_log("Run RMM on the host\n\n");
	rmm_log("Usage: %s [-h|--help] [app_id app_elf [...]]\n\n", app_name);

	rmm_log("Arguments:\n");
	rmm_log("  -h, --help      print this message and exit.\n");
	rmm_log("  app_id          Integer value of app id of the app.\n");
	rmm_log("  app_elf         path to the app's elf file.\n");
}

void process_command_line_arguments(int argc, char *argv[])
{
	int ret __unused;
	int i;
	unsigned int curr_app_index = 0;
	char *end;
	struct app_header *app_header;

	for (i = 1; i < argc; ++i) {
		if (strcmp(argv[i], "--help") == 0 ||
		   strcmp(argv[i], "-h") == 0) {
			print_help(argv[0]);
			exit(0);
		}
		if (curr_app_index >= APP_COUNT) {
			ERROR("Too many apps (more than %d).\n", APP_COUNT);
			exit(1);
		}
		if (i+1 >= argc) {
			ERROR("Invalid number of arguments.\n");
			exit(1);
		}

		ret = app_get_header_ptr_at_index(curr_app_index, &app_header);
		assert(ret == 0);
		app_header->app_id = strtol(argv[i], &end, 0);
		if (end != argv[i] + strlen(argv[i])) {
			ERROR("Invalid app id '%s'.\n", argv[i]);
			exit(1);
		}
		i += 1;
		app_header->app_elf_name = argv[i];
		NOTICE("Registering app at idx %u: id=%lu, filename='%s'\n",
			curr_app_index, app_header->app_id, app_header->app_elf_name);

		/* test opening the image file */
		FILE *f = fopen(app_header->app_elf_name, "rb");

		if (f == NULL) {
			ERROR("Failed to open file '%s'\n", app_header->app_elf_name);
			exit(1);
		}
		size_t bytes_read = fread(&ret, 1U, 1U, f);

		if (bytes_read != 1) {
			ERROR("Failed to read from file '%s'\n", app_header->app_elf_name);
			exit(1);
		}
		ret = fclose(f);
		if (ret != 0) {
			ERROR("Failed to close file during read test'%s'\n",
				app_header->app_elf_name);
			exit(1);
		}
		++curr_app_index;
	}
}

int main(int argc, char *argv[])
{

	process_command_line_arguments(argc, argv);

	VERBOSE("RMM: Beginning of Fake Host execution\n");

	host_util_set_cpuid(0U);

	host_util_setup_sysreg_and_boot_manifest();

	plat_setup(0UL,
		   EL3_IFC_ABI_VERSION,
		   RMM_EL3_MAX_CPUS,
		   (uintptr_t)host_util_get_el3_rmm_shared_buffer());

	/*
	 * Enable the MMU. This is needed as some initialization code
	 * called by rmm_main() asserts that the mmu is enabled.
	 */
	enable_fake_host_mmu();

	/* Start RMM */
	rmm_main();

	/* Create a realm */
	if (create_realm() != 0) {
		ERROR("ERROR: failed to create realm");
		return -1;
	}

	VERBOSE("RMM: Fake Host execution completed\n");

	return 0;
}

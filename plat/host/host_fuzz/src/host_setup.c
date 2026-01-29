/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <attest_app.h>
#include <buffer.h>
#include <debug.h>
#include <dev_assign_app.h>
#include <entropy.h>
#include <fuzzer_protocol.h>
#include <glob_data.h>
#include <granule.h>
#include <harness_utils.h>
#include <host_rmi_wrappers.h>
#include <host_utils.h>
#include <platform_api.h>
#include <random_app.h>
#include <rmm_el3_ifc.h>
#include <signal.h>
#include <smc-rmi.h>
#include <smc-rsi.h>
#include <sro_context.h>
#include <status.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

/* LLVM/GCC gcov runtime: flush .gcda files and reset counters */
extern void __gcov_dump(void);
extern void __gcov_reset(void);

/* Create a simple 4 level (Lvl 0 - LvL 3) RTT structure */
#define RTT_COUNT 4

/*Magic rec_params index that would trigger ripas change flow*/
#define RIPAS_FLOW_MAGIC 99

/* Define the EL3-RMM interface version as set from EL3 */
#define EL3_IFC_ABI_VERSION		\
	RMM_EL3_IFC_MAKE_VERSION(RMM_EL3_IFC_VERS_MAJOR, RMM_EL3_IFC_VERS_MINOR)
#define RMM_EL3_MAX_CPUS		(1U)

extern unsigned long slot_vas[(unsigned int)NR_CPU_SLOTS];

static unsigned int next_granule_index;

/* Instrumentation: track crash context for signal handler */
static volatile uint8_t g_last_command;
static volatile uint64_t g_loop_count;
static volatile const char *g_sro_phase = "none";
static volatile unsigned long g_sro_consumed_entries;

/* Max entries in a granule-sized address list (4096 / sizeof(uintptr_t)) */
#define SRO_ADDR_LIST_MAX_ENTRIES  (GRANULE_SIZE / sizeof(uintptr_t))

/*
 * Persistent SRO state for explicit SRO commands (SRO_DONATE,
 * SRO_RECLAIM, SRO_CONTINUE). These allow the fuzz corpus to drive
 * the SRO protocol step-by-step after REC_CREATE / REC_DESTROY.
 */
static unsigned long sro_ctx_handle;
static unsigned long sro_ctx_donate_req;
static uintptr_t *sro_ctx_addr_list;

static void crash_signal_handler(int sig, siginfo_t *info, void *ctx)
{
	char buf[256];
	int len;

	(void)ctx;
	/* BANNED-API-CHECK[IGNORE] */
	len = snprintf(buf, sizeof(buf),
		       "\n[FUZZ CRASH] sig=%d fault_addr=%p last_cmd=0x%02x "
		       "loop=%llu sro_phase=%s sro_consumed=%lu\n",
		       sig,
		       info ? info->si_addr : (void *)0,
		       (unsigned int)g_last_command,
		       (unsigned long long)g_loop_count,
		       g_sro_phase,
		       g_sro_consumed_entries);
	(void)write(STDERR_FILENO, buf, len);

	/* Reset to default so re-raise terminates with the original signal */
	signal(sig, SIG_DFL);
	raise(sig);
}

static void install_crash_handlers(void)
{
	struct sigaction sa;

	memset(&sa, 0, sizeof(sa));
	sa.sa_sigaction = crash_signal_handler;
	sa.sa_flags = SA_SIGINFO | SA_RESETHAND;
	sigemptyset(&sa.sa_mask);
	sigaction(SIGSEGV, &sa, NULL);
	sigaction(SIGABRT, &sa, NULL);
	sigaction(SIGBUS, &sa, NULL);
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
	unsigned long granule;

	if (next_granule_index >= HOST_NR_GRANULES) {
		return NULL;
	}

	granule = host_util_get_granule_base() + next_granule_index * GRANULE_SIZE;
	++next_granule_index;

	return (void *)granule;
}
static int realm_start(unsigned long *regs, unsigned long *sp_el0);
static int realm_fin(unsigned long *regs, unsigned long *sp_el0);

static int realm_start(unsigned long *regs, unsigned long *sp_el0)
{
	INFO("###########################\n");
	INFO("# Hello World from a Realm!\n");
	INFO("###########################\n");

	regs[0] = SMC_RSI_VERSION;
	regs[1] = MAKE_RSI_REVISION(1, 0);
	return host_util_rsi_helper(realm_fin);
}
static int realm_fin(unsigned long *regs, unsigned long *sp_el0)
{
	INFO("RSI Version is 0x%lx : 0x%lx\n", regs[1], regs[2]);

	if (regs[0] != RSI_SUCCESS) {
		ERROR("RSI_VERSION command failed 0x%lx\n", regs[0]);
		return 0;
	}
	return ARM_EXCEPTION_FIQ_LEL;
}

static int realm_start_ripas(unsigned long *regs, unsigned long *sp_el0);
static int realm_state_set(unsigned long *regs, unsigned long *sp_el0);
static int realm_ripas_fin(unsigned long *regs, unsigned long *sp_el0);

static int realm_start_ripas(unsigned long *regs, unsigned long *sp_el0)
{
	regs[0] = SMC_RSI_IPA_STATE_GET;
	regs[1] = 0x1000;
	regs[2] = 0x2000;
	return host_util_rsi_helper(realm_state_set);
}

static int realm_state_set(unsigned long *regs, unsigned long *sp_el0)
{
	if (regs[0] != RSI_SUCCESS) {
		ERROR("SMC_RSI_IPA_STATE_GET command failed 0x%lx\n", regs[0]);
		return 0;
	}
	INFO("IPA_STATE_GET out_top: 0x%lx, IPA state: 0x%lx\n", regs[1], regs[2]);

	regs[0] = SMC_RSI_IPA_STATE_SET;
	regs[1] = 0x1000;
	regs[2] = 0x2000;
	regs[3] = 0x0;

	return host_util_rsi_helper(realm_ripas_fin);
}

static int realm_ripas_fin(unsigned long *regs, unsigned long *sp_el0)
{
	if (regs[0] != RSI_SUCCESS) {
		ERROR("SMC_RSI_IPA_STATE_SET command failed 0x%lx\n", regs[0]);
		return 0;
	}
	INFO("IPA_STATE_SET new_base: 0x%lx, response: 0x%lx\n", regs[1], regs[2]);

	return ARM_EXCEPTION_FIQ_LEL;
}

uint64_t rmm_main(uint64_t token);
void rmm_arch_init(void);

void handle_ns_smc(unsigned long function_id,
		   unsigned long arg0,
		   unsigned long arg1,
		   unsigned long arg2,
		   unsigned long arg3,
		   unsigned long arg4,
		   unsigned long arg5,
		   unsigned long arg6,
		   struct smc_result *res);

void init(void)
{
	install_crash_handlers();

	host_util_set_cpuid(0U);

	host_util_setup_sysreg_and_boot_manifest();

	arch_features_query_el3_support();

	rmm_arch_init();

	plat_setup(0UL,
		   EL3_IFC_ABI_VERSION,
		   RMM_EL3_MAX_CPUS,
		   (uintptr_t)host_util_get_el3_rmm_shared_buffer(),
		   0UL);

	/*
	 * Enable the MMU. This is needed as some initialization code
	 * called by rmm_main() asserts that the mmu is enabled.
	 */
	enable_fake_host_mmu();

	/* Start RMM */
	(void)rmm_main(0UL);

	/*
	 * Activate RMM: allocate an NS granule to use as the config buffer,
	 * call RMI_RMM_CONFIG_SET then RMI_RMM_ACTIVATE.
	 * This transitions RMM from INIT to ACTIVE state so all other
	 * RMI calls can succeed.
	 */
	struct smc_result activate_res;
	void *config_buf = allocate_granule();

	host_rmi_rmm_config_set((unsigned long)config_buf, &activate_res);
	host_rmm_activate(&activate_res);
}

/*
 * Cancel any in-progress SRO operation to prevent assert in
 * sro_ctx_reserve() when starting a new REC_CREATE/REC_DESTROY.
 */
static void sro_cancel_if_active(struct smc_result *res)
{
	if (sro_ctx_handle != 0UL) {
		host_rmi_op_cancel(sro_ctx_handle, 0UL, res);
		sro_ctx_handle = 0UL;
		sro_ctx_donate_req = 0UL;
	}
}

static inline uintptr_t encode_rmi_addr_desc(uintptr_t base, unsigned long count,
					     unsigned long state)
{
	return INPLACE(RMI_ADDR_RDESC_4K_SZ, RMI_PAGE_L3) |
	       INPLACE(RMI_ADDR_RDESC_4K_CNT, count) |
	       INPLACE(RMI_ADDR_RDESC_4K_ADDR,
		       base >> GRANULE_SHIFT) |
	       INPLACE(RMI_ADDR_RDESC_4K_ST, state);
}

size_t readCorpus(int argc, char *argv[], unsigned char *buffer)
{
	size_t maxlen = 4096;
	size_t read_res = 0;
	FILE *fp = NULL;

	if (argc < 2) {
		return 1;
	}

	fp = fopen(argv[1], "rb");
	if (!fp) {
		return 1;
	}

	read_res = fread(buffer, 1, maxlen, fp);

	if (fclose(fp) || read_res < 1) {
		return 1;
	}

	return read_res;
}

void app_reset(void)
{

	app_processes_cleanup();
	attest_reset_app_state();
	random_reset_app_state();
	arch_reset_entropy();


	/*
	 * Re-initialise the random app PRNG before the attestation app, as the
	 * attestation app global init needs randomness for ECDSA key generation.
	 * Mirrors the order in runtime/core/init.c.
	 */
	random_app_init_prng();


	if (attest_app_global_init() != 0) {
		WARN("Attestation init failed.\n");
	}

	/*
	 * Re-initialise the attestation app per-CPU instance after the state
	 * reset.  attest_reset_app_state() clears attest_app_init_done[], so
	 * any subsequent realm_create (which calls attest_do_hash) would hit
	 * the assert without this call.
	 */
	attest_app_init_per_cpu_instance();
}

/*
 * Lightweight per-iteration reset: only clears granule allocation
 * state and tracking arrays.  Skips the expensive app teardown /
 * crypto-key regeneration done by the full reset().
 */
static void fast_reset(void)
{
	size_t alloc_size;
	uintptr_t alloc;
	size_t sro_sz;
	struct smc_result cancel_res = { 0 };

	/* Cancel any in-progress SRO from the previous iteration */
	sro_cancel_if_active(&cancel_res);

	/* Reset SRO context pool so sro_ctx_reserve() won't assert */
	sro_ctx_reset();
	uintptr_t sro_va = glob_data_get_sro_ctx_va(&sro_sz);
	memset((void *)sro_va, 0, sro_sz);
	sro_ctx_init(sro_va, sro_sz);

	memset(slot_vas, 0, sizeof(slot_vas));

	alloc = glob_data_get_granules_va(&alloc_size);
	memset((void *)alloc, 0, alloc_size);
	alloc = glob_data_get_dev_granules_va(&alloc_size);
	memset((void *)alloc, 0, alloc_size);
	alloc = glob_data_get_vmids_va(&alloc_size);
	memset((void *)alloc, 0, alloc_size);
	alloc = glob_data_get_mec_state_va(&alloc_size);
	memset((void *)alloc, 0, alloc_size);

	next_granule_index = 0;

	sro_ctx_handle = 0UL;
	sro_ctx_donate_req = 0UL;
	sro_ctx_addr_list = NULL;
}

int execute(unsigned char *buffer, size_t read_res)
{
	struct test_buffer b = { 0 };
	struct smc_result res = { 0 };

	b.data = buffer;
	b.length = read_res;
	b.read_index = 0;
	void *_granules[256] = { 0 };

	while (1) {
		uint8_t command = 0;

		if (test_buffer_get_u8(&b, &command) < 0) {
			return 0;
		}

		g_last_command = command;
		switch (command) {
		case COMMAND_ALLOCATE_GRANULE: {
			PACKET(packet_allocate_granule, b, packet);
			_granules[packet.index] = allocate_granule();
			break;
		}

		case COMMAND_VERSION: {
			PACKET(packet_version, b, packet);
			host_rmi_version(packet.req, &res);
			if (res.x[0] == RMI_SUCCESS) {
				INFO("RMI interface version: Low: %lu.%lu High: %lu.%lu\n",
				     RMI_ABI_VERSION_GET_MAJOR(res.x[1]),
				     RMI_ABI_VERSION_GET_MINOR(res.x[1]),
				     RMI_ABI_VERSION_GET_MAJOR(res.x[2]),
				     RMI_ABI_VERSION_GET_MINOR(res.x[2]));
			}
			break;
		}

		case COMMAND_GRANULE_DELEGATE: {
			PACKET(packet_granule_delegate, b, packet);
			host_rmi_granule_range_delegate(
					_granules[packet.index],
					(void *)((uintptr_t)_granules[packet.index] + GRANULE_SIZE),
					&res);
			break;
		}

		case COMMAND_GRANULE_UNDELEGATE: {
			PACKET(packet_granule_undelegate, b, packet);
			host_rmi_granule_range_undelegate(
					_granules[packet.index],
					(void *)((uintptr_t)_granules[packet.index] + GRANULE_SIZE),
					&res);
			break;
		}

		case COMMAND_RTT_DATA_MAP_INIT: {
			PACKET(packet_rtt_data_map_init, b, packet);
			validate_state(_granules[packet.rd_index], GRANULE_STATE_RD)
			validate_state(_granules[packet.data_index], GRANULE_STATE_DELEGATED)
			host_rmi_rtt_data_map_init(
					_granules[packet.rd_index],
					_granules[packet.data_index],
					packet.ipa,
					_granules[packet.src],
					packet.flags,
					&res);
			break;
		}

		case COMMAND_RTT_DATA_UNMAP: {
			PACKET(packet_rtt_data_unmap, b, packet);
			validate_state(_granules[packet.rd_index], GRANULE_STATE_RD)
			host_rmi_rtt_data_unmap(
					_granules[packet.rd_index],
					packet.base,
					packet.top,
					packet.flags,
					0UL,
					&res);
			break;
		}

		case COMMAND_RTT_DATA_MAP: {
			PACKET(packet_rtt_data_map, b, packet);
			validate_state(_granules[packet.rd_index], GRANULE_STATE_RD)
			host_rmi_rtt_data_map(
					_granules[packet.rd_index],
					packet.base,
					packet.top,
					packet.flags,
					packet.oaddr,
					&res);
			break;
		}

		case COMMAND_REALM_ACTIVATE: {
			PACKET(packet_realm_activate, b, packet);
			validate_state(_granules[packet.rd_index], GRANULE_STATE_RD)
			host_rmi_realm_activate(_granules[packet.rd_index], &res);
			break;
		}

		case COMMAND_REALM_CREATE: {
			/* Realm create */
			PACKET(packet_realm_create, b, packet);
			validate_state(_granules[packet.rd_index], GRANULE_STATE_DELEGATED)
			validate_state(_granules[packet.param_index], GRANULE_STATE_NS)
			validate_state(_granules[packet.rtt_base_index], GRANULE_STATE_DELEGATED)

			struct rmi_realm_params *realm_params = _granules[packet.param_index];

			/*
			 * Uninitialized realm_params will hit assert, which we need to avoid.
			 * Null realm_params or wrong granule state, will only emit RMI_INPUT_ERROR,
			 * therefore no need to fill realm_params in that case.
			 */
			if (realm_params && granule_state_is(
					    (uintptr_t)_granules[packet.param_index],
					    GRANULE_STATE_NS)) {
				memset(realm_params, 0, sizeof(*realm_params));

				realm_params->flags0 = packet.flags;
				realm_params->s2sz = packet.s2sz;
				realm_params->sve_vl = packet.sve_vl;
				realm_params->num_bps = packet.num_bps;
				realm_params->num_wps = packet.num_wps;
				realm_params->pmu_num_ctrs = packet.pmu_num_ctrs;
				realm_params->algorithm = packet.hash_algo;
				realm_params->rtt_base =
						(uintptr_t)_granules[packet.rtt_base_index];
				realm_params->rtt_level_start = packet.rtt_level_start;
				realm_params->rtt_num_start = packet.rtt_num_start;
			}

			/*
			 * At this point realm_params will either cause RMI_INPUT_ERROR
			 * or will succeed. We want to explore RMI_INPUT ERROR, so won't restrict
			 */
			host_rmi_realm_create(_granules[packet.rd_index], realm_params, &res);
			break;
		}

		case COMMAND_REALM_DESTROY: {
			PACKET(packet_realm_destroy, b, packet);
			validate_state(_granules[packet.rd_index], GRANULE_STATE_RD)
			host_rmi_realm_destroy(_granules[packet.rd_index], &res);
			break;
		}

		case COMMAND_REC_CREATE: {
			PACKET(packet_rec_create, b, packet);
			validate_state(_granules[packet.rd_index], GRANULE_STATE_RD)
			validate_state(_granules[packet.rec_index], GRANULE_STATE_DELEGATED)
			validate_state(_granules[packet.param_index], GRANULE_STATE_NS)

			struct rmi_rec_params *rec_params = _granules[packet.param_index];
			/*
			 * Uninitialized rec_params will hit assert, which we need to avoid.
			 * Null rec_params or wrong granule state, will only emit RMI_INPUT_ERROR,
			 * therefore no need to fill rec_params in that case.
			 */
			if (rec_params && granule_state_is(
					    (uintptr_t)_granules[packet.param_index],
					    GRANULE_STATE_NS)) {
				memset(rec_params, 0x00, sizeof(*rec_params));
				rec_params->flags = packet.flags;
				rec_params->mpidr = packet.mpidr;
				if (packet.param_index == RIPAS_FLOW_MAGIC) {
					rec_params->pc = (uintptr_t)realm_start_ripas;
				} else {
					rec_params->pc = (uintptr_t)realm_start;
				}

				printf("PC 0x%08lx\n", rec_params->pc);
			}

			sro_cancel_if_active(&res);
			sro_ctx_handle = 0UL;
			sro_ctx_donate_req = 0UL;

			/*
			 * At this point rec_params will either cause RMI_INPUT_ERROR
			 * or will succeed. We want to explore RMI_INPUT ERROR, so won't restrict
			 */
			host_rmi_rec_create(
					_granules[packet.rd_index],
					_granules[packet.rec_index],
					rec_params,
					&sro_ctx_handle, &sro_ctx_donate_req,
					&res);
			break;
		}

		case COMMAND_REC_DESTROY: {
			PACKET(packet_rec_destroy, b, packet);
			validate_state(_granules[packet.rec_index], GRANULE_STATE_REC)

			sro_cancel_if_active(&res);
			sro_ctx_handle = 0UL;
			sro_ctx_donate_req = 0UL;

			host_rmi_rec_destroy(_granules[packet.rec_index],
					     (void *)&sro_ctx_handle, &res);
			break;
		}

		case COMMAND_REC_ENTER: {
			PACKET(packet_rec_enter, b, packet);
			validate_state(_granules[packet.rec_index], GRANULE_STATE_REC)
			validate_state(_granules[packet.run_index], GRANULE_STATE_NS)

			struct rmi_rec_run *rec_run = _granules[packet.run_index];
			if (rec_run && granule_state_is(
					    (uintptr_t)_granules[packet.run_index],
					    GRANULE_STATE_NS)) {
				memset(rec_run, 0x00, sizeof(*rec_run));
			}

			host_rmi_rec_enter(_granules[packet.rec_index], rec_run, &res);
			break;
		}

		case COMMAND_RTT_CREATE: {
			PACKET(packet_rtt_create, b, packet);
			validate_state(_granules[packet.rd_index], GRANULE_STATE_RD)
			validate_state(_granules[packet.rtt_index], GRANULE_STATE_DELEGATED)
			host_rmi_rtt_create(
					_granules[packet.rd_index],
					_granules[packet.rtt_index],
					(void *)packet.ipa,
					packet.level, &res);
			break;
		}

		case COMMAND_RTT_DESTROY: {
			PACKET(packet_rtt_destroy, b, packet);
			validate_state(_granules[packet.rd_index], GRANULE_STATE_RD)
			host_rmi_rtt_destroy(
					_granules[packet.rd_index],
					(void *)packet.ipa,
					packet.level, &res);
			break;
		}

		case COMMAND_RTT_MAP_UNPROTECTED: {
			PACKET(packet_rtt_map_unprotected, b, packet);
			validate_state(_granules[packet.rd_index], GRANULE_STATE_RD)
			host_rmi_rtt_map_unprotected(
					_granules[packet.rd_index],
					packet.ipa,
					packet.level,
					packet.desc, &res);
			break;
		}

		case COMMAND_RTT_READ_ENTRY: {
			PACKET(packet_rtt_read_entry, b, packet);
			validate_state(_granules[packet.rd_index], GRANULE_STATE_RD)
			host_rmi_rtt_read_entry(
					_granules[packet.rd_index],
					packet.ipa,
					packet.level, &res);
			break;
		}

		case COMMAND_RTT_UNMAP_UNPROTECTED: {
			PACKET(packet_rtt_unmap_unprotected, b, packet);
			validate_state(_granules[packet.rd_index], GRANULE_STATE_RD)
			host_rmi_rtt_unmap_unprotected(
					_granules[packet.rd_index],
					packet.ipa,
					packet.level, &res);
			break;
		}

		case COMMAND_PSCI_COMPLETE: {
			PACKET(packet_psci_complete, b, packet);
			validate_state(_granules[packet.calling_rec], GRANULE_STATE_REC)
			validate_state(_granules[packet.target_rec], GRANULE_STATE_REC)
			host_rmi_psci_complete(
					_granules[packet.calling_rec],
					_granules[packet.target_rec],
					packet.status, &res);
			break;
		}

		case COMMAND_FEATURES: {
			PACKET(packet_features, b, packet);
			host_rmi_features(packet.index, &res);
			if (res.x[0] == RMI_SUCCESS) {
				INFO("<i> Feature register value: 0x%08lX\n", res.x[1]);
			}
			break;
		}

		case COMMAND_RTT_FOLD: {
			PACKET(packet_rtt_fold, b, packet);
			validate_state(_granules[packet.rd_index], GRANULE_STATE_RD)
			host_rmi_rtt_fold(
					_granules[packet.rd_index],
					packet.ipa,
					packet.level, &res);
			break;
		}

		case COMMAND_RTT_INIT_RIPAS: {
			PACKET(packet_rtt_init_ripas, b, packet);
			validate_state(_granules[packet.rd_index], GRANULE_STATE_RD)
			host_rmi_rtt_init_ripas(
					_granules[packet.rd_index],
					packet.base, packet.top, &res);
			break;
		}

		case COMMAND_RTT_SET_RIPAS: {
			PACKET(packet_rtt_set_ripas, b, packet);
			validate_state(_granules[packet.rd_index], GRANULE_STATE_RD)
			validate_state(_granules[packet.rec_index], GRANULE_STATE_REC)
			host_rmi_rtt_set_ripas(
					_granules[packet.rd_index],
					_granules[packet.rec_index],
					packet.base, packet.top, &res);
			break;
		}

		case COMMAND_RMM_CONFIG_GET: {
			PACKET(packet_rmm_config_get, b, packet);
			validate_state(_granules[packet.config_index], GRANULE_STATE_NS)
			host_rmi_rmm_config_get(
					(unsigned long)_granules[packet.config_index],
					&res);
			break;
		}

		case COMMAND_RMM_CONFIG_SET: {
			PACKET(packet_rmm_config_set, b, packet);
			validate_state(_granules[packet.config_index], GRANULE_STATE_NS)
			host_rmi_rmm_config_set(
					(unsigned long)_granules[packet.config_index],
					&res);
			break;
		}

		case COMMAND_GRANULE_TRACKING_GET: {
			PACKET(packet_granule_tracking_get, b, packet);
			host_rmi_granule_tracking_get(
					(unsigned long)_granules[packet.granule_index],
					&res);
			break;
		}

		case COMMAND_SRO_DONATE: {
			PACKET(packet_sro_donate, b, packet);
			unsigned long donate_count = (unsigned long)packet.count;

			/*
			 * If count is 0, read from the donate_req returned by
			 * the previous REC_CREATE_SRO / SRO_CONTINUE call.
			 */
			if (donate_count == 0UL) {
				donate_count = EXTRACT(RMI_OP_DONATE_BLK_COUNT,
						       sro_ctx_donate_req);
			}

			/* bound the donate count */
			if (donate_count > 512UL) {
				donate_count = 512UL;
			}

			if (sro_ctx_addr_list == NULL) {
				sro_ctx_addr_list = allocate_granule();
				if (sro_ctx_addr_list == NULL) {
					break;
				}
				memset(sro_ctx_addr_list, 0, GRANULE_SIZE);
			}

			for (unsigned int i = 0U; i < donate_count; i++) {
				void *aux = allocate_granule();

				if (aux == NULL) {
					donate_count = i;
					break;
				}
				uintptr_t aux_addr = (uintptr_t)aux;

				host_rmi_granule_range_delegate(
					aux,
					(void *)(aux_addr + GRANULE_SIZE),
					&res);

				sro_ctx_addr_list[i] = encode_rmi_addr_desc(
					aux_addr, 1UL, RMI_OP_MEM_DELEGATE);
			}

			unsigned long consumed = 0UL;

			g_sro_phase = "donate";
			host_rmi_op_mem_donate(sro_ctx_handle,
					       sro_ctx_addr_list,
					       donate_count,
					       &sro_ctx_donate_req,
					       &consumed, &res);
			g_sro_consumed_entries = consumed;
			break;
		}

		case COMMAND_SRO_RECLAIM: {
			PACKET(packet_sro_reclaim, b, packet);
			unsigned long list_entries = (unsigned long)packet.list_entries;

			/* Bound the list entries */
			if (list_entries > 512UL) {
				list_entries = 512UL;
			}

			if (sro_ctx_addr_list == NULL) {
				sro_ctx_addr_list = allocate_granule();
				if (sro_ctx_addr_list == NULL) {
					break;
				}
				memset(sro_ctx_addr_list, 0, GRANULE_SIZE);
			}

			unsigned long consumed = 0UL;

			g_sro_phase = "reclaim";
			host_rmi_op_mem_reclaim(sro_ctx_handle,
						sro_ctx_addr_list,
						list_entries,
						&consumed, &res);
			g_sro_consumed_entries = consumed;

			if (consumed > SRO_ADDR_LIST_MAX_ENTRIES) {
				ERROR("SRO_RECLAIM: consumed=%lu exceeds max %lu - clamping\n",
				      consumed,
				      (unsigned long)SRO_ADDR_LIST_MAX_ENTRIES);
				consumed = SRO_ADDR_LIST_MAX_ENTRIES;
			}

			g_sro_phase = "reclaim_undelegate";
			for (unsigned int i = 0U; i < consumed; i++) {
				unsigned long entry = (unsigned long)sro_ctx_addr_list[i];
				uintptr_t gptr = EXTRACT(RMI_ADDR_RDESC_4K_ADDR,
							 entry) << GRANULE_SHIFT;
				unsigned long bcnt = EXTRACT(RMI_ADDR_RDESC_4K_CNT,
							    entry);
				bool delegated = (EXTRACT(RMI_ADDR_RDESC_4K_ST,
							  entry) != 0UL);

				if (delegated && bcnt > 0UL) {
					host_rmi_granule_range_undelegate(
						(void *)gptr,
						(void *)(gptr + (bcnt * GRANULE_SIZE)),
						&res);
				}
			}
			break;
		}

		case COMMAND_SRO_CONTINUE: {
			PACKET(packet_sro_continue, b, packet);

			g_sro_phase = "continue";
			host_rmi_op_continue(&sro_ctx_handle, packet.flags,
					     &sro_ctx_donate_req, &res);
			break;
		}

		default: {
			uint8_t args[7] = { 0 };

			if (test_buffer_get_data(&b, args, sizeof(args)) < 0) {
				return 0;
			}

			handle_ns_smc(0xc4000100 | command,
				      args[0], args[1],
				      args[2], args[3],
				      args[4], args[5],
				      args[6],
				      &res);
			break;
		}
		}
		if (res.x[0] != RMI_SUCCESS) {
			ERROR("<!> ====== RMI call failed status = %lu.\n", res.x[0]);
		}
	}
}

#ifdef PERSISTENT_MODE

__AFL_FUZZ_INIT();

#endif

#define MINIMUM_LENGTH_FOR_FUZZING 128

int main(int argc, char *argv[])
{
	host_util_initialise_app_headers(argc, argv);

	VERBOSE("RMM: Beginning of Fake Host execution\n");

	init();

	/*
	 * Flush coverage data for init() before the AFL forkserver starts.
	 * Code before __AFL_INIT() runs only in the parent process, which
	 * never exits cleanly, so its gcov counters would be lost without
	 * an explicit dump here.
	 */
	__gcov_dump();
#ifdef PERSISTENT_MODE

	/*
	 * Kill app processes spawned during init()/rmm_main() before the
	 * fork server starts.  The parent only forks children and never
	 * calls execute(), so its app processes would sit idle forever.
	 * Each AFL child will re-spawn fresh app processes via app_reset().
	 */
	app_processes_cleanup();

	__AFL_INIT();
	app_reset();

	unsigned char *buffer = __AFL_FUZZ_TESTCASE_BUF;

	/* Starting AFL_LOOP */
	while (__AFL_LOOP(10000)) {
		g_loop_count++;
		fast_reset();
		size_t len = __AFL_FUZZ_TESTCASE_LEN;
		/* INFO("Loop: %d Len: %lu\n", loop++, len); */

		if (len < MINIMUM_LENGTH_FOR_FUZZING) {
			continue;
		}
		execute(buffer, len);

		/*
		 * Flush coverage for this iteration, then reset counters
		 * so the next dump writes only new data. Without reset,
		 * accumulated counters would overwrite the init coverage
		 * persisted above.
		 */
		__gcov_dump();
		__gcov_reset();
	}

#else
	unsigned char buffer[4096] = { 0 };
	size_t read_res = readCorpus(argc, argv, buffer);
	execute(buffer, read_res);

#endif

	VERBOSE("RMM: Fake Host execution completed\n");
	app_processes_cleanup();

	return 0;
}

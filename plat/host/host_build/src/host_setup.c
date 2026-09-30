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
#include <pcpu_data.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <s2tt.h>
#include <sizes.h>
#include <smc-rmi.h>
#include <status.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

/* Create a simple 4 level (Lvl 0 - LvL 3) RTT structure */
#define RTT_COUNT 4

/* Define the EL3-RMM interface version as set from EL3 */
#define EL3_IFC_ABI_VERSION		\
	RMM_EL3_IFC_MAKE_VERSION(RMM_EL3_IFC_VERS_MAJOR, RMM_EL3_IFC_VERS_MINOR)
#define RMM_EL3_MAX_CPUS		(1U)

static struct host_realm g_realm;

static unsigned int next_granule_index;

/*
 * Advance the simple Host allocator to @alignment without consuming memory.
 * The boot-only caller supplies a power-of-two granule alignment and enough
 * Host DRAM must remain after the adjustment.
 */
static void align_granule_allocator(unsigned long alignment)
{
	unsigned long base = host_util_get_granule_base();
	unsigned long current = base +
				((unsigned long)next_granule_index * GRANULE_SIZE);
	unsigned long aligned = round_up(current, alignment);

	assert(IS_POWER_OF_TWO(alignment) && GRANULE_ALIGNED(alignment));
	next_granule_index = (unsigned int)((aligned - base) / GRANULE_SIZE);
	assert(next_granule_index < HOST_NR_GRANULES);
}

void *allocate_granule(unsigned int num_granules)
{
	unsigned long granule;

	if ((next_granule_index + num_granules) > HOST_NR_GRANULES) {
		panic();
	}

	granule = host_util_get_granule_base() +
		  next_granule_index * GRANULE_SIZE;
	next_granule_index += num_granules;

	return (void *)granule;
}

void *allocate_granule_aligned(unsigned int num_granules)
{
	unsigned long base = host_util_get_granule_base();
	unsigned long align_bytes = (unsigned long)num_granules * GRANULE_SIZE;
	unsigned long current_addr = base +
				     (unsigned long)next_granule_index * GRANULE_SIZE;

	next_granule_index = (unsigned int)
		((round_up(current_addr, align_bytes) - base) / GRANULE_SIZE);

	return allocate_granule(num_granules);
}

/*
 * Function to emulate the MMU enablement for the fake_host architecture.
 */
static void enable_fake_host_mmu(void)
{
	write_sctlr_el2(SCTLR_ELx_WXN_BIT | SCTLR_ELx_M_BIT);
}

static int delegate_granule_range(void *start_addr, void *end_addr)
{
	struct smc_result result;
	void *start = start_addr;
	void *end = end_addr;

	while ((uintptr_t)start < (uintptr_t)end) {
		host_rmi_granule_range_delegate(start, end, &result);
		CHECK_RMI_RESULT();
		start = (void *)result.x[1];
		if ((uintptr_t)start == 0UL) {
			break;
		}
	}

	return 0;
}

static int undelegate_granule_range(void *start_addr, void *end_addr)
{
	struct smc_result result;
	void *start = start_addr;
	void *end = end_addr;

	while ((uintptr_t)start < (uintptr_t)end) {
		unsigned long handle;
		unsigned long status;

		host_rmi_granule_range_undelegate(start, end, &result);
		status = unpack_return_code(result.x[0]).status;
		handle = result.x[1];
		while (status == RMI_INCOMPLETE) {
			unsigned long donate_req = 0UL;
			unsigned long wrapper_handle = handle;

			if (EXTRACT(RMI_OP_MEM_REQ, result.x[0]) !=
			    RMI_OP_MEM_REQ_NONE) {
				return -1;
			}
			host_rmi_op_continue(&wrapper_handle, 0UL, &donate_req,
					     &result);
			status = unpack_return_code(result.x[0]).status;
		}
		CHECK_RMI_RESULT();
		start = (void *)result.x[1];
		if ((uintptr_t)start == 0UL) {
			break;
		}
	}

	return 0;
}

static unsigned long host_handle_rec_sro(struct smc_result *result,
					 unsigned long handle,
					 unsigned long donate_req)
{
	if (host_sro_drive(handle, result->x[0], donate_req) != 0) {
		return (unsigned long)-1;
	}
	return RMI_SUCCESS;
}

/*
 * Decode the configured Beta 3 tracking-region size. The configuration has
 * already passed RMI validation, so an unknown encoding is an assertion.
 */
static unsigned long host_tracking_region_size(
					const struct rmi_rmm_config *config)
{
	assert(config != NULL);
	if (config->tracking_region_size ==
			RMI_GRAN_4KB_TRACKING_REGION_SIZE_2MB) {
		return SZ_2M;
	}

	assert(config->tracking_region_size ==
			RMI_GRAN_4KB_TRACKING_REGION_SIZE_1GB);
	return SZ_1G;
}

/*
 * Change every tracking region intersecting a Host memory bank to fine
 * tracking. Drive the donation SRO when the selected allocation mode leaves
 * fine-granule pages for the Host to supply. A region already made fine by
 * an adjacent bank is skipped. Return zero on success or -1 when a tracking
 * query, SET_TRACKING, or its SRO fails.
 */
static int host_memory_bank_set_fine(unsigned long base, unsigned long size,
				     unsigned long category,
				     unsigned long region_size)
{
	struct smc_result result;
	unsigned long top = base + size;
	unsigned long addr = round_down(base, region_size);

	while (addr < top) {
		unsigned long query_addr = (addr < base) ? base : addr;
		unsigned long set_category = category;

		/* An adjacent bank may already have made this shared region fine. */
		host_rmi_granule_tracking_get(query_addr,
					       query_addr + GRANULE_SIZE, &result);
		CHECK_RMI_RESULT();
		if (result.x[2] == RMI_TRACKING_FINE) {
			addr += region_size;
			continue;
		}

		/*
		 * The aligned base can belong to an adjacent bank of another
		 * category. SET identifies such a shared region by that base.
		 */
		host_rmi_granule_tracking_get(addr, addr + GRANULE_SIZE, &result);
		CHECK_RMI_RESULT();
		if (result.x[1] != RMI_MEM_CATEGORY_NONE) {
			set_category = result.x[1];
		}

		host_rmi_granule_tracking_set(addr, set_category,
					       RMI_TRACKING_FINE, &result);
		if (result.x[0] != RMI_SUCCESS) {
			if ((unpack_return_code(result.x[0]).status !=
							RMI_INCOMPLETE) ||
			    (host_sro_drive(result.x[1], result.x[0],
					    result.x[2]) != 0)) {
				ERROR("Failed to set tracking to fine at 0x%lx\n",
				      addr);
				return -1;
			}
		}
		addr += region_size;
	}

	return 0;
}

/*
 * Restore a Host bank in descending address order. Full regions return to
 * coarse tracking; boundary regions containing an uncovered address return to
 * NONE because they have no valid coarse representation. Descending order
 * permits higher-address metadata users to release backing pages before their
 * lower-address donor region. Return zero on success or -1 on an RMI failure.
 */
static int host_memory_bank_restore(unsigned long base, unsigned long size,
				    unsigned long category,
				    unsigned long region_size)
{
	struct smc_result result;
	unsigned long bank_top = base + size;
	unsigned long first = round_down(base, region_size);
	unsigned long addr = round_down(bank_top - 1UL, region_size);

	for (;;) {
		unsigned long state = ((addr >= base) &&
					       ((addr + region_size) <= bank_top)) ?
					      RMI_TRACKING_COARSE : RMI_TRACKING_NONE;

		host_rmi_granule_tracking_set(addr, category, state, &result);
		if (result.x[0] != RMI_SUCCESS) {
			if ((unpack_return_code(result.x[0]).status !=
							RMI_INCOMPLETE) ||
			    (host_sro_drive(result.x[1], result.x[0],
					    result.x[2]) != 0)) {
				ERROR("Failed to restore tracking at 0x%lx\n", addr);
				return -1;
			}
		}
		if (addr == first) {
			break;
		}
		addr -= region_size;
	}

	return 0;
}

/*
 * Validate the configured tracking allocation mode and prepare Host memory
 * for the Realm scenario. With RMM_ALLOC_TRACKING_DATA enabled, the
 * struct granule and struct dev_granule arrays are populated at boot and
 * Host memory starts FINE tracked. For the SRO mode, verify that a coarse
 * region rejects a 4 KiB operation, exercise allocation and reclaim, and confirm
 * that it returns to coarse. Finally, enable fine tracking for the Host
 * memory banks used by the scenario. Return zero on success or -1 on an
 * unexpected RMI result.
 */
static int host_tracking_setup(const struct host_realm *realm,
			       unsigned long region_size)
{
	struct smc_result result;
	return_code_t rc;
	uintptr_t rd;
	uintptr_t region_base;

	assert(realm != NULL);
	rd = (uintptr_t)realm->rd;
	region_base = round_down(rd, region_size);

	host_rmi_granule_tracking_get(rd, rd + GRANULE_SIZE, &result);
	CHECK_RMI_RESULT();
	if (result.x[2] != RMI_TRACKING_FINE) {
		if (result.x[2] != RMI_TRACKING_COARSE) {
			ERROR("Expected coarse tracking before SRO validation\n");
			return -1;
		}

		/* Confirm that a coarse granule rejects a 4 KiB operation. */
		host_rmi_granule_range_delegate(realm->rd,
					 (void *)(rd + GRANULE_SIZE), &result);
		rc = unpack_return_code(result.x[0]);

		if ((rc.status != RMI_ERROR_TRACKING) ||
		    (rc.data.level_addr.level != 0U) ||
		    (rc.data.level_addr.addr != rd)) {
			ERROR("Expected RMI_ERROR_TRACKING before fine tracking\n");
			return -1;
		}

		/* Donate fine metadata, validate delegation, then reclaim it. */
		if (host_memory_bank_set_fine(region_base, region_size,
					      RMI_MEM_CATEGORY_CONVENTIONAL,
					      region_size) != 0) {
			ERROR("Failed to enable fine tracking for SRO validation\n");
			return -1;
		}
		if (delegate_granule_range(realm->rd,
					   (void *)(rd + GRANULE_SIZE)) != 0) {
			ERROR("Delegation failed after enabling fine tracking\n");
			return -1;
		}
		if (undelegate_granule_range(realm->rd,
					     (void *)(rd + GRANULE_SIZE)) != 0) {
			ERROR("Failed to restore the tracking-test granule to NS\n");
			return -1;
		}
		if (host_memory_bank_restore(region_base, region_size,
					     RMI_MEM_CATEGORY_CONVENTIONAL,
					     region_size) != 0) {
			ERROR("Failed to reclaim SRO validation metadata\n");
			return -1;
		}

		/* Confirm that reclaim completed the FINE-to-COARSE transition. */
		host_rmi_granule_tracking_get(rd, rd + GRANULE_SIZE, &result);
		CHECK_RMI_RESULT();
		if (result.x[2] != RMI_TRACKING_COARSE) {
			ERROR("Tracking region was not restored to coarse\n");
			return -1;
		}
	}

	/*
	 * Bootstrap this source region with a self-describing metadata page,
	 * which may be donated while undelegated because its fine granule
	 * does not exist yet. Later metadata donations can then use delegated
	 * pages allocated from this fine-tracked region.
	 */
	if (host_memory_bank_set_fine(region_base, region_size,
				      RMI_MEM_CATEGORY_CONVENTIONAL,
				      region_size) != 0) {
		ERROR("Failed to restore the fine-tracking metadata source\n");
		return -1;
	}

	/* Granule operations below require fine tracking for their memory banks. */
	if (host_memory_bank_set_fine(host_util_get_granule_base(),
				      HOST_DRAM_SIZE,
				      RMI_MEM_CATEGORY_CONVENTIONAL,
				      region_size) != 0) {
		ERROR("Failed to enable fine tracking for Host DRAM\n");
		return -1;
	}
	if (host_memory_bank_set_fine(host_util_get_dev_granule_base(),
				      HOST_NCOH_DEV_SIZE,
				      RMI_MEM_CATEGORY_DEV_NCOH,
				      region_size) != 0) {
		ERROR("Failed to enable fine tracking for Host device memory\n");
		return -1;
	}

	return 0;
}

unsigned long host_realm_get_realm_data_1(void)
{
	return (unsigned long)g_realm.realm_data_1;
}

static int rtt_data_map_range(void *rd, uintptr_t base_ipa, uintptr_t top_ipa, uintptr_t base_pa)
{
	struct smc_result result;
	uintptr_t current_ipa = base_ipa;
	uintptr_t current_pa = base_pa;

	while (current_ipa < top_ipa) {
		/*
		 * Build an RmiAddrRangeDesc4KB for one L3 page:
		 *   sz [1:0]    = 0  (L3 page)
		 *   cnt [11:2]  = 1
		 *   addr[51:12] = current_pa >> GRANULE_SHIFT
		 */
		unsigned long desc =
			INPLACE(RMI_ADDR_RDESC_4K_CNT, 1UL) |
			INPLACE(RMI_ADDR_RDESC_4K_ADDR,
				(unsigned long)current_pa >> GRANULE_SHIFT);

		host_rmi_rtt_data_map(rd,
				      current_ipa,
				      top_ipa,
				      RMI_ADDR_TYPE_SINGLE,
				      desc,
				      &result);
		CHECK_RMI_RESULT();

		/* Update IPA for next iteration */
		current_ipa = result.x[1];
		if (current_ipa >= top_ipa) {
			break;
		}

		/* Calculate corresponding PA */
		current_pa = base_pa + (current_ipa - base_ipa);
	}

	return 0;
}

static int rtt_data_unmap_range(void *rd, uintptr_t base_ipa, uintptr_t top_ipa)
{
	struct smc_result result;
	uintptr_t current_ipa = base_ipa;

	while (current_ipa < top_ipa) {
		host_rmi_rtt_data_unmap(rd,
					current_ipa,
					top_ipa,
					0x1UL,
					0UL,
					&result);
		CHECK_RMI_RESULT();

		/* Update IPA for next iteration */
		current_ipa = result.x[1];
		if (current_ipa >= top_ipa) {
			break;
		}
	}

	return 0;
}

/*
 * Activate RMM, validate dynamic tracking metadata, and construct one Realm.
 * The caller supplies persistent Host-owned Realm storage. Return zero after
 * the Realm is active, or -1 when any RMI or SRO operation fails.
 */
static int host_create_realm_and_activate(struct host_realm *realm)
{
	struct smc_result result;
	struct rmi_rmm_config *config;
	unsigned long region_size;
	unsigned long feat_reg2;
	unsigned int i;
	u_register_t create_handle = 0UL;
	u_register_t donate_req = 0UL;

	/* Use an interior, homogeneous 2 MiB region for the first Realm objects. */
	align_granule_allocator(SZ_2M);

	/* Allocate granules */
	realm->rd = allocate_granule(1);
	realm->rec = allocate_granule(1);
	realm->rec_params = allocate_granule(1);
	realm->rec_run = allocate_granule(1);
	realm->realm_params = allocate_granule(1);

	host_rmi_version(MAKE_RMI_REVISION(2, 0), &result);

	CHECK_RMI_RESULT();
	INFO("RMI Version is 0x%lx : 0x%lx\n", result.x[1], result.x[2]);

	/* Check if DA enabled in RMI features */
	host_rmi_features(RMI_FEATURE_REGISTER_2_INDEX, &result);
	CHECK_RMI_RESULT();

	feat_reg2 = result.x[1];

	/* Query all 4 RMI feature registers */
	for (unsigned int i = 0; i < 5; i++) {
		host_rmi_features(i, &result);
		CHECK_RMI_RESULT();
		INFO("RMI_FEATURES(%u) = 0x%lx\n", i, result.x[1]);
	}

	/* Test RMI_GRANULE_TRACKING_GET */
	host_rmi_granule_tracking_get(0, GRANULE_SIZE, &result);
	CHECK_RMI_RESULT();
	INFO("RMI_GRANULE_TRACKING_GET: category=0x%lx, tracking=0x%lx\n",
	     result.x[1], result.x[2]);

	/* Test RMI_RMM_CONFIG_GET and RMI_RMM_CONFIG_SET */
	config = (struct rmi_rmm_config *)allocate_granule(1);
	host_rmi_rmm_config_get((unsigned long)config, &result);
	CHECK_RMI_RESULT();
	INFO("RMI_RMM_CONFIG_GET succeeded\n");

	config->tracking_region_size =
			RMI_GRAN_4KB_TRACKING_REGION_SIZE_2MB;
	host_rmi_rmm_config_set((unsigned long)config, &result);
	CHECK_RMI_RESULT();
	INFO("RMI_RMM_CONFIG_SET succeeded\n");
	region_size = host_tracking_region_size(config);

	host_rmm_activate(&result);
	if (result.x[0] != RMI_SUCCESS) {
		ERROR("Failed to activate RMM\n");
		return -1;
	}

	if (host_tracking_setup(realm, region_size) != 0) {
		return -1;
	}

	/* Delegate rd */
	if (delegate_granule_range(realm->rd, (void *)((uintptr_t)realm->rd + GRANULE_SIZE)) != 0) {
		return -1;
	}

	/* Delegate rec */
	if (delegate_granule_range(realm->rec, (void *)((uintptr_t)realm->rec + GRANULE_SIZE)) != 0) {
		return -1;
	}
	/* Allocate all RTT granules first */
	for (i = 0; i < RTT_COUNT; ++i) {
		realm->rtts[i] = allocate_granule(1);
	}

	/* Delegate all RTT granules as a range */
	if (delegate_granule_range(realm->rtts[0],
				   (void *)((uintptr_t)realm->rtts[RTT_COUNT - 1] + GRANULE_SIZE)) != 0) {
		return -1;
	}

	memset(realm->realm_params, 0, sizeof(*realm->realm_params));
	realm->realm_params->s2sz = arch_feat_get_pa_width();
	realm->realm_params->rtt_num_start = 1;
	realm->realm_params->rtt_base = (uintptr_t)realm->rtts[0];
	realm->realm_params->num_bps = 1;
	realm->realm_params->num_wps = 1;

	/* Set Realm flags with DA enabled */
	if (EXTRACT(RMI_FEATURE_REGISTER_2_DA_EN, feat_reg2) ==
	    RMI_FEATURE_TRUE) {
		realm->realm_params->flags0 = INPLACE(RMI_REALM_FLAGS0_DA,
						      RMI_FEATURE_TRUE);
	} else {
		realm->realm_params->flags0 = INPLACE(RMI_REALM_FLAGS0_DA,
						      RMI_FEATURE_FALSE);
	}

	host_rmi_realm_create(realm->rd, realm->realm_params,
			      &create_handle, &donate_req, &result);
	if (host_handle_rec_sro(&result, create_handle, donate_req) != 0) {
		return -1;
	}


	/* Create RTT table to start at IPA 0x0 */
	for (i = 1; i < RTT_COUNT; ++i) {
		host_rmi_rtt_create(realm->rd, realm->rtts[i], 0, i, &result);
		CHECK_RMI_RESULT();
	}

	realm->realm_data_1 = (uintptr_t)allocate_granule(3);
	realm->realm_data_1_num_gr = 3;
	if (delegate_granule_range((void *)realm->realm_data_1,
				   (void *)(realm->realm_data_1 + 3 * GRANULE_SIZE)) != 0) {
		return -1;
	}

	host_rmi_rtt_init_ripas(realm->rd, REALM_BUFFER_IPA_1,
				REALM_BUFFER_IPA_1 + (realm->realm_data_1_num_gr * GRANULE_SIZE),
				&result);
	CHECK_RMI_RESULT();

	/* Map data granules as a range */
	if (rtt_data_map_range(realm->rd, REALM_BUFFER_IPA_1,
			       REALM_BUFFER_IPA_1 + (realm->realm_data_1_num_gr * GRANULE_SIZE),
			       realm->realm_data_1) != 0) {
		return -1;
	}

	realm->rec_params->flags |= REC_PARAMS_FLAG_RUNNABLE;
	realm->rec_params->pc = (uintptr_t)realm_start;

	host_rmi_rec_create(realm->rd, realm->rec, realm->rec_params,
			    &create_handle, &donate_req, &result);
	if (host_handle_rec_sro(&result, create_handle, donate_req) != 0) {
		return -1;
	}
	host_rmi_realm_activate(realm->rd, &result);
	CHECK_RMI_RESULT();

	return 0;
}

static int host_destroy_realm(struct host_realm *realm)
{
	struct smc_result result;
	unsigned long i;
	u_register_t destroy_handle = 0UL;
	u_register_t donate_req = 0UL;

	assert(realm != NULL);

	host_rmi_rec_destroy(realm->rec, (void *)&destroy_handle, &result);
	if (host_handle_rec_sro(&result, destroy_handle, donate_req) != 0) {
		return -1;
	}

	/* Unmap data granules as a range */
	if (rtt_data_unmap_range(realm->rd, REALM_BUFFER_IPA_1,
				 REALM_BUFFER_IPA_1 +
				 (realm->realm_data_1_num_gr * GRANULE_SIZE)) != 0) {
		return -1;
	}

	if (undelegate_granule_range((void *)realm->realm_data_1,
		(void *)(realm->realm_data_1 + (realm->realm_data_1_num_gr * GRANULE_SIZE))) != 0) {
		return -1;
	}

	for (i = RTT_COUNT - 1; i >= 1; --i) {
		host_rmi_rtt_destroy(realm->rd, 0, i, &result);
		CHECK_RMI_RESULT();
	}

	/* Undelegate all RTT granules as a range */
	if (undelegate_granule_range(realm->rtts[1],
				     (void *)((uintptr_t)realm->rtts[RTT_COUNT - 1] +
					     GRANULE_SIZE)) != 0) {
		return -1;
	}

	host_rmi_realm_terminate(realm->rd, &result);
	CHECK_RMI_RESULT();

	host_rmi_realm_destroy(realm->rd, (void *)&destroy_handle, &result);
	if (host_handle_rec_sro(&result, destroy_handle, donate_req) != 0) {
		return -1;
	}
	if (undelegate_granule_range(realm->rd,
				     (void *)((uintptr_t)realm->rd + GRANULE_SIZE)) != 0) {
		return -1;
	}
	if (undelegate_granule_range(realm->rec,
				     (void *)((uintptr_t)realm->rec + GRANULE_SIZE)) != 0) {
		return -1;
	}

	return 0;
}

static int host_realm_run_attest(struct host_realm *realm)
{
	struct smc_result result;

	/* Execute the Realm */
	memset(realm->rec_run, 0, sizeof(*realm->rec_run));
	host_rmi_rec_enter(realm->rec, realm->rec_run, &result);
	CHECK_RMI_RESULT();

	while (realm->rec_run->exit.exit_reason == RMI_EXIT_IRQ) {
		/* Clear the IRQ in ISR_EL1 and re-enter Realm */
		host_write_sysreg("isr_el1", 0x0);
		host_rmi_rec_enter(realm->rec, realm->rec_run, &result);
		CHECK_RMI_RESULT();
	}

	if (realm->rec_run->exit.exit_reason == RMI_EXIT_FIQ) {
		INFO("Realm executed successfully and exited due to FIQ.\n");
		return 0;
	}

	ERROR("Unexpected REC exit reason during attestation flow: %lu\n",
		realm->rec_run->exit.exit_reason);
	return -1;
}

uint64_t rmm_main(void);
void rmm_arch_init(void);

int main(int argc, char *argv[])
{
	int host_pdev_id = 0;
	int host_vdev_id = -1;
	int rc = 0;
	bool realm_created = false;

	host_util_pas_enable(true);
	host_util_initialise_app_headers(argc, argv);

	char *base_dir = host_util_get_base_dir(argv[0]);

	host_util_launch_spdm_responder_emu(base_dir);
	free(base_dir);

	VERBOSE("RMM: Beginning of Fake Host execution\n");

	host_util_set_cpuid(0U);

	/* host_util_rec_run() only enters registered Realm callbacks. */
	host_util_set_realm_entry(realm_start);

	host_util_setup_sysreg_and_boot_manifest();

	/*
	 * Fake-host builds do not execute the EL2 assembly entry path, so set up
	 * the current CPU's metadata page here instead.
	 */
	pcpu_fake_host_setup(0U, 0UL);

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
	(void)rmm_main();

	/* Create a realm and a rec */
	if (host_create_realm_and_activate(&g_realm) != 0) {
		ERROR("ERROR: failed to create realm");
		rc = -1;
		goto out_cleanup;
	}
	realm_created = true;

	/*
	 * Find devices (spdm_responder) and if any device exist create a PDEV
	 * instance of the device with RMM and establish a secure session with
	 * the device so that the device is in a assignable state to a Realm.
	 */
	host_pdev_id = host_pdev_probe_and_setup();
	if (host_pdev_id == -1) {
		ERROR("ERROR: host_device_init failed.\n");
		rc = -1;
		goto out_cleanup;
	}

	/* Run rec to invoke attest related RSIs */
	rc = host_realm_run_attest(&g_realm);
	if (rc != 0) {
		ERROR("ERROR: host_realm_rec_run_attest_rsi failed\n");
		goto out_cleanup;
	}

	/* Create vdev instance and bind with the Realm */
	if (host_pdev_id > 0) {
		/* Activate PSMMU and create L2 stream table for device SID */
		rc = host_psmmu_setup(0U, 0x100UL);
		if (rc != 0) {
			ERROR("ERROR: host_psmmu_setup failed\n");
			goto out_cleanup;
		}

		INFO("host: Assign vdev_tdi_id 0x%x to rd:\n", host_pdev_id);
		host_vdev_id = host_vdev_assign(&g_realm,
						(unsigned long)host_pdev_id);
		if (host_vdev_id < 0) {
			ERROR("ERROR: host_device_assign_to_realm\n");
			rc = -1;
			goto out_cleanup;
		}

		/* Run rec to invoke DA related RSIs */
		rc = host_realm_run_da(&g_realm);
		if (rc != 0) {
			ERROR("ERROR: host_realm_run_da_rsi failed\n");
			goto out_cleanup;
		}
	}

out_cleanup:
	/* Stop the VDEV and do vdev_destroy */
	if (host_vdev_id >= 0) {
		if (host_vdev_reclaim(&g_realm, host_vdev_id) != 0) {
			ERROR("ERROR: host_vdev_reclaim failed\n");
			rc = -1;
		}
	}

	/*
	 * This calls PDEV STOP and terminate secure session and calls
	 * PDEV DESTROY
	 */
	if (host_pdev_id > 0) {
		if (host_pdev_reclaim(host_pdev_id) != 0) {
			ERROR("ERROR: host_pdev_reclaim failed\n");
			rc = -1;
		}
	}

	/* Stop the SPDM responder process */
	host_util_stop_spdm_responder();

	if (realm_created) {
		/* Destroy the realm and all related resources */
		(void)host_destroy_realm(&g_realm);
	}

	INFO("RMM: Fake Host execution completed\n");

	return rc;
}

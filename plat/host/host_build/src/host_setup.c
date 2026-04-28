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
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <s2tt.h>
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

void *allocate_granule(unsigned int num_granules)
{
	static unsigned int next_granule_index;
	unsigned long granule;

	if ((next_granule_index + num_granules) > HOST_NR_GRANULES) {
		panic();
	}

	granule = host_util_get_granule_base() +
		  next_granule_index * GRANULE_SIZE;
	next_granule_index += num_granules;

	return (void *)granule;
}

/*
 * Function to emulate the MMU enablement for the fake_host architecture.
 */
static void enable_fake_host_mmu(void)
{
	write_sctlr_el2(SCTLR_ELx_WXN_BIT | SCTLR_ELx_M_BIT);
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
		host_rmi_granule_range_undelegate(start, end, &result);
		CHECK_RMI_RESULT();
		start = (void *)result.x[1];
		if ((uintptr_t)start == 0UL) {
			break;
		}
	}

	return 0;
}

static uintptr_t rec_allocate_aux(unsigned long granules, bool delegate)
{

	uintptr_t aux = (uintptr_t)allocate_granule(granules);

	/* Delegate all rec_aux granules as a range if needed */
	if (delegate) {
		(void)delegate_granule_range((void *)aux,
					   (void *)(aux + (granules * GRANULE_SIZE)));
	}

	return aux;
}

static void rec_free_aux(uintptr_t granules_ptr, unsigned long granules, bool delegated)
{
	if (delegated) {
		bool undelegated __unused;

	       /* undelegate all the aux granules */
		undelegated = undelegate_granule_range((void *)granules_ptr,
					 (void *)(granules_ptr + (granules * GRANULE_SIZE)));

		assert(undelegated);
	}
}

static unsigned long host_handle_rec_sro(struct host_realm *realm,
					 struct smc_result *result,
					 unsigned long *handle,
					 unsigned long *donate_req)
{
	unsigned long ret_status = result->x[0];

	return_code_t rc = unpack_return_code(ret_status);

	while (rc.status == RMI_INCOMPLETE) {
		unsigned long mem_req = EXTRACT(RMI_OP_MEM_REQ, ret_status);
		unsigned long consumed_entries __unused = 0UL;

		switch (mem_req) {
		case RMI_OP_MEM_REQ_DONATE: {
			unsigned long count = EXTRACT(RMI_OP_DONATE_BLK_COUNT, *donate_req);
			unsigned long delegate = (*donate_req & MASK(RMI_OP_DONATE_MEM_STATE)) ?
					RMI_OP_MEM_UNDELEGATED : RMI_OP_MEM_DELEGATED;
			uintptr_t base;

			if ((count == 0UL) || (count > MAX_REC_AUX_GRANULES) ||
			    (realm->sro_addr_list_entries == 0UL)) {
				ERROR("Invalid REC aux donate request: count=%lu\n", count);
				return -1;
			}

			/* Ensure we request block of L3 size */
			assert(EXTRACT(RMI_OP_DONATE_BLK_SIZE, *donate_req) == RMI_PAGE_L3);
			base = rec_allocate_aux(count, (delegate == RMI_OP_MEM_DELEGATED));

			/* Populate the list. Add one block (page) per entry */
			for (unsigned int i = 0U; i < count; i++) {
				uintptr_t base_addr = base + (i * GRANULE_SIZE);
				realm->sro_addr_list[i] =
					encode_rmi_addr_desc(base_addr, 1UL, RMI_OP_MEM_DELEGATED);
			}

			host_rmi_op_mem_donate(*handle, realm->sro_addr_list, count,
					       donate_req, &consumed_entries,
					       result);

			/* We expect to have consumed all the entries */
			assert(consumed_entries == count);
			break;
		}
		case RMI_OP_MEM_REQ_RECLAIM: {
			unsigned long total_freed __unused = 0UL;

			host_rmi_op_mem_reclaim(*handle, realm->sro_addr_list,
						realm->sro_addr_list_entries,
						&consumed_entries,
						result);

			for (unsigned int i = 0U; i < consumed_entries; i++) {
				unsigned long entry =
					(unsigned long)realm->sro_addr_list[i];
				uintptr_t granule_ptr;
				unsigned long block_count;
				bool delegated;

				/* Expect the block size to be L3 block */
				assert(EXTRACT(RMI_ADDR_RDESC_4K_SZ, entry) ==
									RMI_PAGE_L3);

				block_count = EXTRACT(RMI_ADDR_RDESC_4K_CNT, entry);
				granule_ptr = EXTRACT(RMI_ADDR_RDESC_4K_ADDR, entry) <<
							GRANULE_SHIFT;
				delegated = (EXTRACT(RMI_ADDR_RDESC_4K_ST, entry) != 0UL);

				rec_free_aux(granule_ptr, block_count, delegated);
				total_freed += block_count;
			}

			/* All aux granules must have been returned */
			assert(total_freed == MAX_REC_AUX_GRANULES);
			break;
		}
		case RMI_OP_MEM_REQ_NONE:
		default:
			host_rmi_op_continue(handle, 0UL, donate_req, result);
			break;
		}

		if ((rc.status != RMI_INCOMPLETE) && (rc.status != RMI_BUSY)) {
			/*
			 * The memory operation failed, issue a RMI_OP_CONTINUE
			 * to inform the host.
			 */
			ret_status = result->x[0];
			unpack_return_code(ret_status);

			host_rmi_op_continue(handle, 0UL, donate_req, result);
		}

		ret_status = result->x[0];
		rc = unpack_return_code(ret_status);
	}

	return result->x[0];
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
		host_rmi_rtt_data_map(rd,
				      current_ipa,
				      top_ipa,
				      0x1UL,
				      current_pa,
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

static int host_create_realm_and_activate(struct host_realm *realm)
{
	struct smc_result result;
	unsigned long feat_reg2;
	unsigned int i;
	u_register_t create_handle = 0UL;
	u_register_t donate_req = 0UL;

	/* Allocate granules */
	realm->rd = allocate_granule(1);
	realm->rec = allocate_granule(1);
	realm->rec_params = allocate_granule(1);
	realm->rec_run = allocate_granule(1);
	realm->realm_params = allocate_granule(1);
	realm->sro_addr_list = allocate_granule(1);
	realm->sro_addr_list_entries = GRANULE_SIZE / sizeof(uintptr_t);
	memset(realm->sro_addr_list, 0, GRANULE_SIZE);

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
	host_rmi_granule_tracking_get(0, &result);
	CHECK_RMI_RESULT();
	INFO("RMI_GRANULE_TRACKING_GET: category=0x%lx, tracking=0x%lx\n",
	     result.x[1], result.x[2]);

	/* Test RMI_RMM_CONFIG_GET and RMI_RMM_CONFIG_SET */
	void *config_buf = allocate_granule(1);
	host_rmi_rmm_config_get((unsigned long)config_buf, &result);
	CHECK_RMI_RESULT();
	INFO("RMI_RMM_CONFIG_GET succeeded\n");

	host_rmi_rmm_config_set((unsigned long)config_buf, &result);
	CHECK_RMI_RESULT();
	INFO("RMI_RMM_CONFIG_SET succeeded\n");

	host_rmm_activate(&result);
	CHECK_RMI_RESULT();

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

	host_rmi_realm_create(realm->rd, realm->realm_params, &result);
	CHECK_RMI_RESULT();

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
	if (host_handle_rec_sro(realm, &result, &create_handle, &donate_req) != 0) {
		return -1;
	}
	CHECK_RMI_RESULT();
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
	if (host_handle_rec_sro(realm, &result, &destroy_handle, &donate_req) != 0) {
		return -1;
	}
	CHECK_RMI_RESULT();

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

	host_rmi_realm_destroy(realm->rd, &result);
	CHECK_RMI_RESULT();
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
	}

	return 0;
}

uint64_t rmm_main(uint64_t token);
void rmm_arch_init(void);

int main(int argc, char *argv[])
{
	int host_pdev_id = 0;
	int host_vdev_id = -1;
	int rc = 0;
	bool realm_created = false;

	host_util_initialise_app_headers(argc, argv);

	char *base_dir = host_util_get_base_dir(argv[0]);

	host_util_launch_spdm_responder_emu(base_dir);
	free(base_dir);

	VERBOSE("RMM: Beginning of Fake Host execution\n");

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

	VERBOSE("RMM: Fake Host execution completed\n");

	return rc;
}

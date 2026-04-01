/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <host_realm.h>
#include <host_utils.h>
#include <smc-rsi.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Unassigned vdev_id to validate VdevIdIsFree() failure handling. */
#define HOST_DA_FREE_VDEV_ID	(HOST_DA_VDEV_ID + 1UL)

/*
 * Check previous RSI result and finish realm part of RSI flow.
 */
static int host_realm_da_rsi_call_end(unsigned long *rec_regs, unsigned long *rec_sp_el0)
{
	const struct rsi_vdev_info *vdev_info;
	unsigned long vsmmu;

	(void)rec_sp_el0;

	INFO(" > Realm: RSI_VDEV_GET_INFO with valid arg completed\n");
	if (rec_regs[0] != RSI_SUCCESS) {
		ERROR("RSI_VDEV_GET_INFO failed 0x%lx\n", rec_regs[0]);
		return 0;
	}

	/*
	 * The VDEV info was written by RMM to REALM_BUFFER_IPA. In fake host,
	 * this is directly accessible via the host-mapped realm buffer address.
	 */
	vdev_info = (const struct rsi_vdev_info *)host_realm_get_realm_data_1();
	assert(vdev_info != NULL);

	vsmmu = EXTRACT(RSI_VDEV_FLAGS_VSMMU, vdev_info->flags);
	INFO("=================================================\n");
	INFO(" vdev_info (IPA=0x%lx, VA=0x%lx)\n",
	     (unsigned long)REALM_BUFFER_IPA, (unsigned long)vdev_info);
	INFO(" flags=0x%lx (vsmmu=%lu)\n", vdev_info->flags, vsmmu);
	INFO(" cert_id=0x%lx\n", vdev_info->cert_id);
	INFO(" hash_algo=%u\n", (unsigned int)vdev_info->hash_algo);
	INFO(" lock_nonce=0x%lx\n", vdev_info->lock_nonce);
	INFO(" meas_nonce=0x%lx\n", vdev_info->meas_nonce);
	INFO(" report_nonce=0x%lx\n", vdev_info->report_nonce);
	INFO(" format_type=%u\n", (unsigned int)vdev_info->format_type);
	INFO(" format_version=0x%lx\n", vdev_info->format_version);
	INFO(" state=%u\n", (unsigned int)vdev_info->state);
	INFO(" vsmmu_addr=0x%lx\n", vdev_info->vsmmu_addr);
	INFO(" vsmmu_vsid=0x%lx\n", vdev_info->vsmmu_vsid);

	VERBOSE(" vca_digest (%u bytes):", RSI_VDEV_VCA_DIGEST_LEN);
	print_buf(vdev_info->vca_digest, RSI_VDEV_VCA_DIGEST_LEN);
	VERBOSE(" cert_digest (%u bytes):", RSI_VDEV_CERT_DIGEST_LEN);
	print_buf(vdev_info->cert_digest, RSI_VDEV_CERT_DIGEST_LEN);
	VERBOSE(" pubkey_digest (%u bytes):", RSI_VDEV_PUBKEY_DIGEST_LEN);
	print_buf(vdev_info->pubkey_digest, RSI_VDEV_PUBKEY_DIGEST_LEN);
	VERBOSE(" meas_digest (%u bytes):", RSI_VDEV_MEAS_DIGEST_LEN);
	print_buf(vdev_info->meas_digest, RSI_VDEV_MEAS_DIGEST_LEN);
	VERBOSE(" report_digest (%u bytes):", RSI_VDEV_REPORT_DIGEST_LEN);
	print_buf(vdev_info->report_digest, RSI_VDEV_REPORT_DIGEST_LEN);

	INFO("=================================================\n");
	return ARM_EXCEPTION_FIQ_LEL;
}

/*
 * Check previous RSI result
 * Calls RSI_VDEV_GET_INFO with valid VDEV id and valid IPA.
 * Should return RSI_SUCCESS, RmiRecExitReason: RMI_EXIT_VDEV_REQUEST
 */
static int host_realm_da_rsi_call_2(unsigned long *rec_regs, unsigned long *rec_sp_el0)
{
	(void)rec_sp_el0;

	if (rec_regs[0] != RSI_ERROR_INPUT) {
		ERROR("Expected RSI_ERROR_INPUT for EMPTY RIPAS, got 0x%lx\n", rec_regs[0]);
		return 0;
	}
	/* Try an assigned VDEV id and expect success. */
	INFO(" > Realm: Calling RSI_VDEV_GET_INFO: valid vdev_id & valid IPA\n");

	rec_regs[0] = SMC_RSI_VDEV_GET_INFO;
	rec_regs[1] = HOST_DA_VDEV_ID;		/* Valid vdev_id */
	rec_regs[2] = REALM_BUFFER_IPA;		/* Valid IPA */
	return host_util_rsi_helper(host_realm_da_rsi_call_end);
}

/*
 * Check previous RSI result
 * Calls RSI_VDEV_GET_INFO with valid VDEV id but invalid IPA.
 * Should return RSI_ERROR_INPUT
 */
static int host_realm_da_rsi_call_1(unsigned long *rec_regs, unsigned long *rec_sp_el0)
{
	(void)rec_sp_el0;

	if (rec_regs[0] != RSI_ERROR_INPUT) {
		ERROR("Expected RSI_ERROR_INPUT for free VDEV id, got 0x%lx\n", rec_regs[0]);
		return 0;
	}
	/* Try an assigned VDEV id and expect success. */
	INFO(" > Realm: Calling RSI_VDEV_GET_INFO: valid vdev_id & invalid IPA\n");

	rec_regs[0] = SMC_RSI_VDEV_GET_INFO;
	rec_regs[1] = HOST_DA_VDEV_ID;		/* Valid vdev_id */
	rec_regs[2] = REALM_BUFFER_IPA_2;	/* Invalid IPA */
	return host_util_rsi_helper(host_realm_da_rsi_call_2);
}

/*
 * Call RSI_VDEV_GET_INFO with free VDEV id.
 * Should return RSI_ERROR_INPUT
 */
int host_realm_da_rsi_main(unsigned long *rec_regs, unsigned long *rec_sp_el0)
{
	(void)rec_sp_el0;

	INFO("###########################\n");
	INFO("# Hello World from a Realm!\n");
	INFO("###########################\n");
	INFO(" > Realm: Calling RSI_VDEV_GET_INFO: invalid vdev_id & valid IPA\n");

	/* First call uses an unassigned VDEV id and must fail with RSI_ERROR_INPUT. */
	rec_regs[0] = SMC_RSI_VDEV_GET_INFO;
	rec_regs[1] = HOST_DA_FREE_VDEV_ID;	/* Invalid vdev_id */
	rec_regs[2] = REALM_BUFFER_IPA;		/* Valid IPA */

	return host_util_rsi_helper(host_realm_da_rsi_call_1);
}

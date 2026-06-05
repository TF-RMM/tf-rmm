/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <host_realm.h>
#include <host_utils.h>
#include <minicoro.h>
#include <smc-rsi.h>
#include <string.h>

/* Unassigned vdev_id to validate VdevIdIsFree() failure handling. */
#define HOST_DA_FREE_VDEV_ID	(HOST_DA_VDEV_ID + 1UL)

/*
 * DA RSI coroutine.
 * Uses shared g_rec_regs/g_realm_ret from host_realm_attest_rsi.c.
 */
void realm_da_rsi_coro(mco_coro *co)
{
	const struct rsi_vdev_info *vdev_info;
	unsigned long vsmmu;

	INFO("###########################\n");
	INFO("# Hello World from a Realm!\n");
	INFO("###########################\n");

	/*
	 * Call 1: RSI_VDEV_GET_INFO with free VDEV id.
	 * Should return RSI_ERROR_INPUT
	 */
	INFO(" > Realm: Calling RSI_VDEV_GET_INFO: invalid vdev_id & valid IPA\n");
	g_rec_regs[0] = SMC_RSI_VDEV_GET_INFO;
	g_rec_regs[1] = HOST_DA_FREE_VDEV_ID;		/* Invalid vdev_id */
	g_rec_regs[2] = REALM_BUFFER_IPA;		/* Valid IPA */
	realm_rsi_call(co);

	if (g_rec_regs[0] != RSI_ERROR_INPUT) {
		ERROR("Expected RSI_ERROR_INPUT for free VDEV id, got 0x%lx\n",
		      g_rec_regs[0]);
		g_realm_ret = ARM_EXCEPTION_SYNC_LEL;
		return;
	}

	/*
	 * Call 2: RSI_VDEV_GET_INFO with valid VDEV id but invalid IPA.
	 * Should return RSI_ERROR_INPUT
	 */
	INFO(" > Realm: Calling RSI_VDEV_GET_INFO: valid vdev_id & invalid IPA\n");
	g_rec_regs[0] = SMC_RSI_VDEV_GET_INFO;
	g_rec_regs[1] = HOST_DA_VDEV_ID;		/* Valid vdev_id */
	g_rec_regs[2] = REALM_BUFFER_IPA_2;		/* Invalid IPA */
	realm_rsi_call(co);

	if (g_rec_regs[0] != RSI_ERROR_INPUT) {
		ERROR("Expected RSI_ERROR_INPUT for EMPTY RIPAS, got 0x%lx\n",
		      g_rec_regs[0]);
		g_realm_ret = ARM_EXCEPTION_SYNC_LEL;
		return;
	}

	/*
	 * Call 3: RSI_VDEV_GET_INFO with valid VDEV id and valid IPA.
	 * Should return RSI_SUCCESS
	 */
	INFO(" > Realm: Calling RSI_VDEV_GET_INFO: valid vdev_id & valid IPA\n");
	g_rec_regs[0] = SMC_RSI_VDEV_GET_INFO;
	g_rec_regs[1] = HOST_DA_VDEV_ID;		/* Valid vdev_id */
	g_rec_regs[2] = REALM_BUFFER_IPA;		/* Valid IPA */
	realm_rsi_call(co);

	INFO(" > Realm: RSI_VDEV_GET_INFO with valid arg completed\n");
	if (g_rec_regs[0] != RSI_SUCCESS) {
		ERROR("RSI_VDEV_GET_INFO failed 0x%lx\n", g_rec_regs[0]);
		g_realm_ret = ARM_EXCEPTION_SYNC_LEL;
		return;
	}

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
	g_realm_ret = ARM_EXCEPTION_FIQ_LEL;
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 * Unit tests for SMMUv3 TLBI submission and CMD_SYNC completion.
 *
 * Inspect TLBI fields, MSI completion writes and command order in fake_host
 * queues. Active PSMMU tests also cover deferred completion, timeouts,
 * broadcast maintenance and the shared fixture's device lifecycle.
 * API lists identify the behavior under test; calls used only for setup
 * or inspection are omitted. Indirect API coverage is explicitly marked.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <host_utils.h>
#include <mmio.h>
#include <s2tt.h>
#include <smc-rmi.h>
#include <smmuv3.h>
#include <smmuv3_arch.h>
#include <smmuv3_priv.h>
#include <smmuv3_psmmu.h>
#include <stddef.h>
#include <test_helpers.h>
}

/* Exercise CMD_SYNC handling without active PSMMU setup. */
TEST_GROUP(smmuv3_tlbi)
{
};

/*
 * Return commands since the @start_prod snapshot of this active PSMMU.
 * Tests run without concurrent submissions and must not overwrite a full queue.
 */
static unsigned long tlbi_test_smmu_command_count(const struct smmuv3_dev *smmu,
						uint32_t start_prod)
{
	uint32_t queue_entries = U(1) << smmu->config.cmdq_log2size;
	uint32_t prod = read32(smmu->cmdq.prod_reg);
	uint32_t cons = read32(smmu->cmdq.cons_reg);
	uint32_t count = (prod - start_prod) & ((queue_entries << 1) - 1U);

	/* The inspected sequence must fit in the ring without overwriting itself. */
	CHECK_TRUE(count <= queue_entries);
	/* Only inspect completed sequences: every published command must be consumed. */
	UNSIGNED_LONGS_EQUAL(prod, cons);
	return count;
}

/*
 * Return a command relative to @start_prod in this active PSMMU's queue.
 * @index must be below command_count(); the test must not overwrite the queue.
 */
static uint128_t tlbi_test_smmu_command(const struct smmuv3_dev *smmu, uint32_t start_prod,
				       unsigned long index)
{
	const uint128_t *cmdq = (const uint128_t *)smmu->cmdq.q_base;
	uint32_t queue_entries = U(1) << smmu->config.cmdq_log2size;

	/* Reject an index beyond this submission before reading a potentially stale slot. */
	CHECK_TRUE(index < tlbi_test_smmu_command_count(smmu, start_prod));
	return cmdq[(start_prod + index) & (queue_entries - 1U)];
}

/*
 * Check the range, level hint, and leaf hint of a 4KB TLBI on this PSMMU.
 * @index is relative to @start_prod; the active queue must not be overwritten.
 */
static void tlbi_test_smmu_check_tlbi(const struct smmuv3_dev *smmu, uint32_t start_prod,
				     unsigned long index, unsigned int vmid,
				     unsigned long ipa, unsigned long size,
				     unsigned long ttl, bool leaf)
{
	uint128_t cmd = tlbi_test_smmu_command(smmu, start_prod, index);
	uint64_t lo = (uint64_t)cmd;
	uint64_t hi = (uint64_t)(cmd >> 64);
	unsigned long coverage = (((lo >> NUM_SHIFT) & 0x1FUL) + 1UL) <<
				 ((lo >> SCALE_SHIFT) & 0x1FUL);

	/* The requested range must use the stage-2 IPA invalidation opcode. */
	UNSIGNED_LONGS_EQUAL(CMD_TLBI_S2_IPA, lo & 0xFFUL);
	/* Each list entry must invalidate the address space belonging to its VMID. */
	UNSIGNED_LONGS_EQUAL(vmid, EXTRACT(VMID, lo));
	/* Isolate the IPA bits from the hints and verify the range starts at the requested base. */
	UNSIGNED_LONGS_EQUAL(ipa, hi & BIT_MASK_ULL(55U, 12U));
	/* Decode NUM/SCALE to bytes to catch confusion between mapping counts and granules. */
	UNSIGNED_LONGS_EQUAL(size, coverage * GRANULE_SIZE);
	/* Page and block mappings both use the fixture's 4KB translation granule. */
	UNSIGNED_LONGS_EQUAL(TG_4KB, EXTRACT(TG, hi));
	/* The TTL hint must retain the requested mapping level for this invalidation. */
	UNSIGNED_LONGS_EQUAL(ttl, EXTRACT(TTL, hi));
	/* Preserve whether the caller requested invalidation of leaf entries only. */
	CHECK_EQUAL(leaf, (hi & LEAF_BIT) != 0UL);
}

static struct smmuv3_dev *smmu;

/*
 * Shared setup boots RMM, activates both PSMMUs through RMI and reserves
 * their donated backing outside test allocations. The inspected device
 * lacks FEAT_BTM, so its queue exposes explicit TLBI commands. The other
 * device supplies the BTM and per-device pause comparisons. Teardown resumes
 * the inspected queue while fixture-owned MSI destinations are still alive.
 */
TEST_GROUP(smmuv3_tlbi_active_psmmu)
{
	/* Keep deferred MSI destinations alive through teardown after a failed check. */
	struct smmuv3_cmd_sync pending_sync = {};
	uint32_t later_completion = UINT32_MAX;

	/* Activate both host PSMMUs before a test can pause either command queue. */
	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start(TEST_HELPERS_SMMU);
		for (unsigned int i = 0U; i < HOST_NR_SMMUS; i++) {
			struct smmuv3_dev *dev = smmuv3_psmmu_find(host_util_get_smmu_ns_base(i));

			/* Startup must register each configured host device. */
			CHECK_TRUE(dev != NULL);
			/* Driver operations require active devices with usable queues. */
			CHECK_EQUAL(PSMMU_ACTIVE, dev->state);
		}
		smmu = smmuv3_psmmu_find(host_util_get_smmu_ns_base(TEST_HELPERS_SMMU_IDX));
		/* This device must need explicit TLBIs rather than broadcast maintenance. */
		CHECK_EQUAL(0U, smmu->config.features & FEAT_BTM);
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
	}

	/* Drain deferred writes while the fixture's completion buffers are still alive. */
	TEST_TEARDOWN()
	{
		CHECK_EQUAL(0, smmuv3_arch_pause_cmd_sync(smmu, false));
	}
};

/*
 * Verify an unhinted one-page command, optionally after a 64-page range.
 * @pages must be 1 or 65. The caller must boot the host RMM first; the
 * shared test setup must have activated the non-BTM host PSMMU.
 */
static void check_unhinted_single_page_command(unsigned long pages)
{
	uint32_t start_prod;
	struct smmuv3_cmd_sync sync = {};
	unsigned long base = 1UL << 29;
	unsigned long last = (pages == 1UL) ? 0UL : 1UL;
	uint128_t cmd;
	uint64_t lo, hi;

	CHECK_TRUE((pages == 1UL) || (pages == 65UL));

	start_prod = read32(smmu->cmdq.prod_reg);
	CHECK_EQUAL(0, smmuv3_cmd_sync_init(&sync, (uintptr_t)&sync));
	CHECK_EQUAL(0, smmuv3_inv_at_level(2U, base, 3L, pages, false, &sync));
	cmd = tlbi_test_smmu_command(smmu, start_prod, last);
	lo = (uint64_t)cmd;
	hi = (uint64_t)(cmd >> 64);

	/* The tail command must use the stage-2 IPA invalidation opcode. */
	UNSIGNED_LONGS_EQUAL(CMD_TLBI_S2_IPA, lo & 0xFFUL);
	/* The command invalidates VMID 2, matching the fixture's Realm VMID. */
	UNSIGNED_LONGS_EQUAL(2UL, EXTRACT(VMID, lo));
	/* The command targets the final page, either the only page or the range tail. */
	UNSIGNED_LONGS_EQUAL(base + (pages - 1UL) * GRANULE_SIZE,
			     hi & BIT_MASK_ULL(55U, 12U));
	/* Unhinted one-page encodings must leave TG clear. */
	UNSIGNED_LONGS_EQUAL(0UL, EXTRACT(TG, hi));
	/* Non-leaf invalidations must not carry a TTL hint. */
	UNSIGNED_LONGS_EQUAL(0UL, EXTRACT(TTL, hi));
	/* A table invalidation must not be restricted to leaf entries. */
	CHECK_FALSE((hi & LEAF_BIT) != 0UL);
	/* NUM and SCALE both zero encode a single-page non-range invalidation. */
	UNSIGNED_LONGS_EQUAL(0UL, EXTRACT(NUM, lo));
	UNSIGNED_LONGS_EQUAL(0UL, EXTRACT(SCALE, lo));
	if (pages != 1UL) {
		tlbi_test_smmu_check_tlbi(smmu, start_prod, 0UL, 2U, base,
					(pages - 1UL) * GRANULE_SIZE, 0UL, false);
	}
	/* The host PSMMU uses MSI completion followed by a SEV CMD_SYNC. */
	UNSIGNED_LONGS_EQUAL(last + 3UL, tlbi_test_smmu_command_count(smmu, start_prod));
}

/*
 * TC1: Encode an unhinted single page without a reserved range.
 *
 * Public APIs tested:
 *   smmuv3_inv_at_level(), smmuv3_cmd_sync_init().
 *
 * Aim:
 *   Verify that a non-leaf request with no TTL hint avoids the reserved TG !=
 *   0, NUM = SCALE = TTL = 0 range encoding.
 *
 * Method:
 *   Use the active non-BTM PSMMU fixture. Submit one level-3 page at
 *   IPA 1UL << 29 for VMID 2 with leaf=false. Decode the TLBI and inspect
 *   the consumed command count.
 *
 * Expected results:
 *   The call succeeds. The command retains the IPA and VMID, clears LEAF and
 *   encodes TG, TTL, NUM and SCALE as zero. Exactly three commands are
 *   consumed: the TLBI and its MSI/SEV completion pair.
 */
TEST(smmuv3_tlbi_active_psmmu, unhinted_single_page_tlbi_uses_nonrange_encoding)
{
	check_unhinted_single_page_command(1UL);
}

/*
 * TC2: Encode the final page of an unhinted range legally.
 *
 * Public APIs tested:
 *   smmuv3_inv_at_level(), smmuv3_cmd_sync_init().
 *
 * Aim:
 *   Verify that range decomposition switches to non-range encoding for a
 *   one-page remainder without losing coverage or adding a TTL hint.
 *
 * Method:
 *   On the active non-BTM fixture, invalidate 65 level-3 pages from
 *   IPA 1UL << 29 for VMID 2 with leaf=false. Inspect both TLBIs and the
 *   consumed command count.
 *
 * Expected results:
 *   The first TLBI covers 64 pages using TG_4KB, TTL zero and LEAF clear. The
 *   second targets base + 64 * GRANULE_SIZE with TG, TTL, NUM and SCALE zero
 *   and LEAF clear. Four commands, including one MSI/SEV pair, are consumed.
 */
TEST(smmuv3_tlbi_active_psmmu, unhinted_range_tail_uses_nonrange_encoding)
{
	check_unhinted_single_page_command(65UL);
}

/*
 * TC3: Invalidate removed-table coverage without level hints.
 *
 * Public APIs tested:
 *   smmuv3_inv_at_level_per_vmids_submit(), smmuv3_cmd_sync_is_complete().
 *
 * Aim:
 *   Verify that an invalidation for a removed table covers all of its entries
 *   without restricting the leaf levels affected by the command.
 *
 * Method:
 *   With both host PSMMUs active, submit S2TTES_PER_S2TT entries for VMID 2
 *   at IPA 1UL << 30. Repeat at entry levels 2 and 3, corresponding to
 *   removed L1 and L2 tables. Inspect the non-BTM device queue and completion
 *   object.
 *
 * Expected results:
 *   Submission succeeds and the host emulator reports completion. The TLBI
 *   retains VMID/base, uses TG_4KB with TTL zero and LEAF clear, and covers
 *   1GB or 2MB respectively. Each request consumes one TLBI and one MSI/SEV
 *   pair.
 */
TEST(smmuv3_tlbi_active_psmmu, removed_tables_invalidate_all_walk_levels)
{
	struct smmuv3_cmd_sync sync = {};
	unsigned int vmids[] = {2U};
	unsigned long base = 1UL << 30;

	CHECK_EQUAL(0, smmuv3_cmd_sync_init(&sync, (uintptr_t)&sync));
	for (long level = 2L; level <= 3L; level++) {
		uint32_t start_prod = read32(smmu->cmdq.prod_reg);

		CHECK_EQUAL(0, smmuv3_inv_at_level_per_vmids_submit(vmids, ARRAY_SIZE(vmids),
				base, level, S2TTES_PER_S2TT, false, &sync));
		CHECK_TRUE(smmuv3_cmd_sync_is_complete(&sync));
		tlbi_test_smmu_check_tlbi(smmu, start_prod, 0UL, 2U, base,
					XLAT_BLOCK_SIZE(level - 1L), 0UL, false);
		UNSIGNED_LONGS_EQUAL(3UL, tlbi_test_smmu_command_count(smmu, start_prod));
	}
}

/*
 * TC4: Preserve page and block invalidation hints.
 *
 * Public APIs tested:
 *   smmuv3_inv_at_level().
 *
 * Aim:
 *   Verify conversion from a mapping count to 4KB granules: one level-2
 *   block covers 512 granules, while one level-3 page covers one granule.
 *   Preserve the requested VMID, IPA, level hint and leaf hint.
 *
 * Method:
 *   Call smmuv3_inv_at_level() for one level-2 block and one level-3 page,
 *   using VMID 2 and the same aligned IPA. Decode each TLBI and check the
 *   number of commands consumed by the non-BTM PSMMU.
 *
 * Expected results:
 *   Both calls return 0. Each TLBI covers the full mapping size (2MB or 4KB),
 *   with the requested VMID and IPA, matching TTL, 4KB granule and leaf bit.
 *   Each call consumes three commands: TLBI, MSI CMD_SYNC and SEV CMD_SYNC.
 */
TEST(smmuv3_tlbi_active_psmmu, leaf_page_and_block_preserve_level_hint)
{
	struct smmuv3_cmd_sync sync = {};
	unsigned long base = 1UL << 30;

	CHECK_EQUAL(0, smmuv3_cmd_sync_init(&sync, (uintptr_t)&sync));
	for (long level = 2L; level <= 3L; level++) {
		uint32_t start_prod = read32(smmu->cmdq.prod_reg);

		CHECK_EQUAL(0, smmuv3_inv_at_level(2U, base, level, 1UL, true, &sync));
		/* Verify VMID, IPA, mapping-sized coverage, granule, TTL and leaf bit. */
		tlbi_test_smmu_check_tlbi(smmu, start_prod, 0UL, 2U, base,
					XLAT_BLOCK_SIZE(level), (unsigned long)level, true);
		/* One TLBI and its MSI/SEV completion pair must be fully consumed. */
		UNSIGNED_LONGS_EQUAL(3UL, tlbi_test_smmu_command_count(smmu, start_prod));
	}
}

/*
 * TC5: Invalidate every VMID with one shared completion sequence.
 *
 * Public APIs tested:
 *   smmuv3_inv_at_level_per_vmids().
 *
 * Aim:
 *   Verify that a synchronous VMID-list request emits one invalidation per
 *   VMID in list order and shares synchronization across the list.
 *
 * Method:
 *   Invalidate the same level-3 page for VMIDs 2 and 1, in that order, using
 *   smmuv3_inv_at_level_per_vmids(). Inspect both TLBIs and the command count.
 *
 * Expected results:
 *   The call returns 0. The two TLBIs retain VMID order, IPA, page size,
 *   4KB granule, TTL 3 and the leaf bit. Four commands are consumed: the two
 *   TLBIs followed by one shared MSI/SEV completion pair.
 */
TEST(smmuv3_tlbi_active_psmmu, vmid_list_emits_each_invalidation)
{
	struct smmuv3_cmd_sync sync = {};
	unsigned int vmids[] = {2U, 1U};
	unsigned long base = 1UL << 29;
	uint32_t start_prod = read32(smmu->cmdq.prod_reg);

	CHECK_EQUAL(0, smmuv3_cmd_sync_init(&sync, (uintptr_t)&sync));
	CHECK_EQUAL(0, smmuv3_inv_at_level_per_vmids(vmids, ARRAY_SIZE(vmids),
			base, 3L, 1UL, true, &sync));
	for (unsigned int i = 0U; i < ARRAY_SIZE(vmids); i++) {
		/* Match each list entry to a page TLBI with the same IPA and hints. */
		tlbi_test_smmu_check_tlbi(smmu, start_prod, i, vmids[i], base,
					GRANULE_SIZE, 3UL, true);
	}
	/* Two TLBIs must share one MSI/SEV pair, giving four consumed commands. */
	UNSIGNED_LONGS_EQUAL(4UL, tlbi_test_smmu_command_count(smmu, start_prod));
}

/*
 * TC6: Preserve asynchronous invalidation fields and completion commands.
 *
 * Public APIs tested:
 *   smmuv3_inv_at_level_per_vmids_submit(), smmuv3_cmd_sync_is_complete().
 *
 * Aim:
 *   Verify that asynchronous VMID-list submission preserves range and hint
 *   fields and appends the correct MSI/SEV completion sequence.
 *
 * Method:
 *   Submit leaf mappings and full TABLE ranges for VMIDs 2 and 1 via
 *   smmuv3_inv_at_level_per_vmids_submit(). Decode all four commands for each
 *   request and query completion with fake_host processing left unpaused.
 *
 * Expected results:
 *   Each submission returns 0 and consumes two TLBIs in VMID order, with the
 *   requested IPA and coverage; only leaf requests carry TTL. The following
 *   MSI CMD_SYNC writes zero to this PSMMU's completion word, followed by a
 *   SIG_SEV CMD_SYNC. Immediate fake_host processing leaves the object complete.
 */
TEST(smmuv3_tlbi_active_psmmu, async_vmid_list_preserves_range_and_hints)
{
	struct smmuv3_cmd_sync sync = {};
	unsigned int vmids[] = {2U, 1U};
	unsigned long base = 1UL << 30;

	CHECK_EQUAL(0, smmuv3_cmd_sync_init(&sync, (uintptr_t)&sync));
	for (long level = 2L; level <= 3L; level++) {
		for (bool leaf : {false, true}) {
			uint32_t start_prod = read32(smmu->cmdq.prod_reg);
			unsigned long count = leaf ? 1UL : S2TTES_PER_S2TT;
			unsigned long size = count * XLAT_BLOCK_SIZE(level);
			uint128_t cmd;
			uint64_t lo, hi;

			CHECK_EQUAL(0, smmuv3_inv_at_level_per_vmids_submit(vmids,
					ARRAY_SIZE(vmids), base, level, count, leaf, &sync));
			for (unsigned int i = 0U; i < ARRAY_SIZE(vmids); i++) {
				tlbi_test_smmu_check_tlbi(smmu, start_prod, i, vmids[i],
					base, size, leaf ? (unsigned long)level : 0UL, leaf);
			}
			/* Two VMID TLBIs share one MSI/SEV pair. */
			UNSIGNED_LONGS_EQUAL(4UL,
				tlbi_test_smmu_command_count(smmu, start_prod));
			cmd = tlbi_test_smmu_command(smmu, start_prod, ARRAY_SIZE(vmids));
			lo = (uint64_t)cmd;
			hi = (uint64_t)(cmd >> MSIADDR_SHIFT);
			/* The first completion command writes the MSI completion word. */
			UNSIGNED_LONGS_EQUAL(CMD_SYNC, EXTRACT(CMD, lo));
			UNSIGNED_LONGS_EQUAL(SIG_IRQ, EXTRACT(CS, lo));
			UNSIGNED_LONGS_EQUAL(0UL, lo >> MSIDATA_SHIFT);
			UNSIGNED_LONGS_EQUAL((uintptr_t)&sync.completion[TEST_HELPERS_SMMU_IDX],
					     hi);
			cmd = tlbi_test_smmu_command(smmu, start_prod, ARRAY_SIZE(vmids) + 1U);
			lo = (uint64_t)cmd;
			/* The second completion command wakes waiters with SEV. */
			UNSIGNED_LONGS_EQUAL(CMD_SYNC, EXTRACT(CMD, lo));
			UNSIGNED_LONGS_EQUAL(SIG_SEV, EXTRACT(CS, lo));
			CHECK_TRUE(smmuv3_cmd_sync_is_complete(&sync));
		}
	}
}

/*
 * TC7: Select event signalling for regular CMD_SYNC.
 *
 * Public APIs tested:
 *   None.
 *
 * Internal helper tested:
 *   prepare_send_command().
 *
 * Aim:
 *   Verify CMD_SYNC event selection and consumption on a device with FEAT_SEV.
 *   This checks command encoding; fake_host does not emulate a CPU wake-up.
 *
 * Method:
 *   Configure a small fake_host queue with FEAT_SEV and submit a regular
 *   CMD_SYNC through prepare_send_command(). Inspect the command and indices.
 *
 * Expected results:
 *   Submission returns 0, the command encodes CMD_SYNC with SIG_SEV, and the
 *   consumer catches up with the producer.
 */
TEST(smmuv3_tlbi, cmd_sync_sev_command)
{
	uint8_t r_page[GRANULE_SIZE] = {};
	uint128_t cmdq[2] = {};
	uint32_t prod = 0U;
	uint32_t cons = 0U;
	struct smmuv3_dev smmu = {};
	uint64_t cmd_lo;

	smmu.r_base = (uintptr_t)r_page;
	smmu.config.features = FEAT_SEV;
	smmu.config.cmdq_log2size = 1U;
	smmu.cmdq.q_base = (uintptr_t)cmdq;
	smmu.cmdq.prod_reg = &prod;
	smmu.cmdq.cons_reg = &cons;

	/* Regular queue synchronization must work on an event-capable device. */
	LONGS_EQUAL(0L, prepare_send_command(&smmu, CMD_SYNC, 0UL, 0UL));
	cmd_lo = (uint64_t)cmdq[0];

	/* The queue entry must encode the requested synchronization operation. */
	UNSIGNED_LONGS_EQUAL(CMD_SYNC, cmd_lo & UINT64_C(0xFF));
	/* FEAT_SEV must select event notification for a waiting CPU. */
	UNSIGNED_LONGS_EQUAL(SIG_SEV, EXTRACT(CS, cmd_lo));
	/* fake_host must consume the event-signalling command and empty the queue. */
	UNSIGNED_LONGS_EQUAL(prod, cons);
}

/*
 * TC8: Synchronize by queue polling without MSI or event signalling.
 *
 * Public APIs tested:
 *   None.
 *
 * Internal helpers tested:
 *   prepare_send_command(), wait_cmdq_empty().
 *
 * Aim:
 *   Verify regular CMD_SYNC completion through queue-index polling when
 *   neither FEAT_MSI nor FEAT_SEV is available.
 *
 * Method:
 *   Configure a fake_host device with only FEAT_BTM, submit a regular CMD_SYNC,
 *   inspect its encoding and call wait_cmdq_empty() after processing.
 *
 * Expected results:
 *   Submission returns 0, the command encodes CMD_SYNC with SIG_NONE, and
 *   wait_cmdq_empty() returns 0 after fake_host consumes the command.
 */
TEST(smmuv3_tlbi, cmd_sync_poll_without_msi)
{
	uint8_t r_page[GRANULE_SIZE] = {};
	uint128_t cmdq[2] = {};
	uint32_t prod = 0U;
	uint32_t cons = 0U;
	struct smmuv3_dev smmu = {};
	uint64_t cmd_lo;

	smmu.r_base = (uintptr_t)r_page;
	smmu.config.features = FEAT_BTM;
	smmu.config.cmdq_log2size = 1U;
	smmu.cmdq.q_base = (uintptr_t)cmdq;
	smmu.cmdq.prod_reg = &prod;
	smmu.cmdq.cons_reg = &cons;

	/* Regular CMD_SYNC submission must succeed without MSI or event support. */
	LONGS_EQUAL(0L, prepare_send_command(&smmu, CMD_SYNC, 0UL, 0UL));
	cmd_lo = (uint64_t)cmdq[0];

	/* Lack of signalling support must still leave a CMD_SYNC in the queue. */
	UNSIGNED_LONGS_EQUAL(CMD_SYNC, cmd_lo & UINT64_C(0xFF));
	/* Neither an unsupported MSI write nor an event may be requested. */
	UNSIGNED_LONGS_EQUAL(SIG_NONE, EXTRACT(CS, cmd_lo));
	/* Consumed queue indices alone must be sufficient to report completion. */
	LONGS_EQUAL(0L, wait_cmdq_empty(&smmu));
}

/*
 * TC9: Defer completion and the following event command on one PSMMU.
 *
 * Public APIs tested:
 *   smmuv3_inv_at_level_per_vmids_submit(), smmuv3_cmd_sync_is_complete().
 *
 * Internal helpers tested:
 *   wait_cmdq_empty(), prepare_send_command(), smmuv3_arch_pause_cmd_sync()
 *   (fake_host control).
 *
 * Aim:
 *   Verify that pausing CMD_SYNC defers the MSI completion and following SEV
 *   command, preserves pending state on timeout, and affects only that PSMMU.
 *
 * Method:
 *   Pause the non-BTM PSMMU and submit one page invalidation asynchronously.
 *   Inspect completion and queue indices, call wait_cmdq_empty(), submit a
 *   CMD_SYNC to the other PSMMU, then resume the paused queue and recheck.
 *
 * Expected results:
 *   The idle object reports complete. Submission returns 0 and publishes
 *   three commands, but only the TLBI is consumed while paused. The MSI word
 *   stays UINT32_MAX and completion is false. Polling returns -ETIMEDOUT
 *   without changing either state. The other PSMMU consumes its CMD_SYNC.
 *   Resuming writes zero, makes completion true and drains all three commands.
 */
TEST(smmuv3_tlbi_active_psmmu, paused_cmd_sync_defers_completion_and_wakeup)
{
	struct smmuv3_dev *btm_smmu = smmuv3_psmmu_find(host_util_get_smmu_ns_base(0U));
	unsigned int vmid = 1U;
	uint32_t start_prod = read32(smmu->cmdq.prod_reg);
	uint32_t mask = (U(1) << (smmu->config.cmdq_log2size + 1U)) - 1U;
	uint32_t btm_start_prod = read32(btm_smmu->cmdq.prod_reg);

	CHECK_EQUAL(0, smmuv3_cmd_sync_init(&pending_sync, (uintptr_t)&pending_sync));
	/* Stop CMD_SYNC execution on this device before publishing any commands. */
	CHECK_EQUAL(0, smmuv3_arch_pause_cmd_sync(smmu, true));
	/* Pausing the device cannot change the state of an idle completion object. */
	CHECK_TRUE(smmuv3_cmd_sync_is_complete(&pending_sync));
	/* Submission must succeed even though its completion cannot run yet. */
	CHECK_EQUAL(0, smmuv3_inv_at_level_per_vmids_submit(&vmid, 1U,
				0UL, S2TT_PAGE_LEVEL, 1UL, true, &pending_sync));
	/* The paused MSI write must leave the actual word at the pending sentinel. */
	UNSIGNED_LONGS_EQUAL(UINT32_MAX, pending_sync.completion[TEST_HELPERS_SMMU_IDX]);
	/* The public query must observe the outstanding completion word. */
	CHECK_FALSE(smmuv3_cmd_sync_is_complete(&pending_sync));
	/* Only the TLBI may be consumed before execution reaches the paused sync. */
	UNSIGNED_LONGS_EQUAL((start_prod + 1U) & mask, read32(smmu->cmdq.cons_reg));
	/* Submission must publish the TLBI and both the MSI and SEV CMD_SYNCs. */
	UNSIGNED_LONGS_EQUAL((start_prod + 3U) & mask, read32(smmu->cmdq.prod_reg));
	/* Polling must time out while CMD_SYNC prevents the queue from draining. */
	LONGS_EQUAL(-ETIMEDOUT, wait_cmdq_empty(smmu));
	/* The polling path must not force the consumer past the paused command. */
	UNSIGNED_LONGS_EQUAL((start_prod + 1U) & mask, read32(smmu->cmdq.cons_reg));
	/* A timeout must not manufacture an MSI completion write. */
	UNSIGNED_LONGS_EQUAL(UINT32_MAX, pending_sync.completion[TEST_HELPERS_SMMU_IDX]);

	/* A pause on one PSMMU must not prevent another from accepting CMD_SYNC. */
	CHECK_EQUAL(0, prepare_send_command(btm_smmu, CMD_SYNC, 0UL, 0UL));
	/* The other device must consume its command while the first stays paused. */
	UNSIGNED_LONGS_EQUAL(1UL, tlbi_test_smmu_command_count(btm_smmu, btm_start_prod));
	/* Resuming must process deferred commands while their storage is valid. */
	CHECK_EQUAL(0, smmuv3_arch_pause_cmd_sync(smmu, false));
	/* Processing the deferred MSI must write the completion value to memory. */
	UNSIGNED_LONGS_EQUAL(0U, pending_sync.completion[TEST_HELPERS_SMMU_IDX]);
	/* All per-SMMU words must now permit the caller to observe completion. */
	CHECK_TRUE(smmuv3_cmd_sync_is_complete(&pending_sync));
	/* The original TLBI and its MSI/SEV pair must all have been consumed. */
	UNSIGNED_LONGS_EQUAL(3UL, tlbi_test_smmu_command_count(smmu, start_prod));
}

/*
 * TC10: Time out a synchronous invalidation while CMD_SYNC is paused.
 *
 * Public APIs tested:
 *   smmuv3_inv_at_level_per_vmids(), smmuv3_cmd_sync_is_complete().
 *
 * Aim:
 *   Verify that the synchronous API waits for the actual MSI completion and
 *   preserves an outstanding operation when its completion polling times out.
 *
 * Method:
 *   Pause CMD_SYNC and invalidate one page through the synchronous VMID-list
 *   API. Inspect the MSI word and completion query, then resume the queue with
 *   the completion object still alive and check completion and queue indices.
 *
 * Expected results:
 *   The API returns -ETIMEDOUT, the MSI word remains UINT32_MAX and completion
 *   is false. Resuming makes completion true and the consumer equals the
 *   producer, including consumption of the following SEV CMD_SYNC.
 */
TEST(smmuv3_tlbi_active_psmmu, paused_cmd_sync_blocks_synchronous_invalidation)
{
	unsigned int vmid = 1U;

	CHECK_EQUAL(0, smmuv3_cmd_sync_init(&pending_sync, (uintptr_t)&pending_sync));
	/* Prevent the MSI completion write before entering the synchronous API. */
	CHECK_EQUAL(0, smmuv3_arch_pause_cmd_sync(smmu, true));
	/* Completion polling must exhaust its retries while the MSI is deferred. */
	LONGS_EQUAL(-ETIMEDOUT, smmuv3_inv_at_level_per_vmids(&vmid, 1U,
			0UL, S2TT_PAGE_LEVEL, 1UL, true, &pending_sync));
	/* Returning an error must preserve the outstanding completion sentinel. */
	UNSIGNED_LONGS_EQUAL(UINT32_MAX, pending_sync.completion[TEST_HELPERS_SMMU_IDX]);
	/* The separate completion query must agree that the operation is pending. */
	CHECK_FALSE(smmuv3_cmd_sync_is_complete(&pending_sync));
	/* The queued operation must remain resumable after the caller timed out. */
	CHECK_EQUAL(0, smmuv3_arch_pause_cmd_sync(smmu, false));
	/* Draining the deferred MSI must make the existing operation complete. */
	CHECK_TRUE(smmuv3_cmd_sync_is_complete(&pending_sync));
	/* The following wake-up CMD_SYNC must also have left the queue. */
	UNSIGNED_LONGS_EQUAL(read32(smmu->cmdq.prod_reg), read32(smmu->cmdq.cons_reg));
}

/*
 * TC11: Preserve deferred MSI write order across a queue wrap.
 *
 * Public APIs tested:
 *   smmuv3_inv_at_level_per_vmids_submit(), smmuv3_cmd_sync_is_complete().
 *
 * Internal helpers tested:
 *   prepare_send_cmd_sync(), smmuv3_arch_pause_cmd_sync() (fake_host control).
 *
 * Aim:
 *   Verify wrap-bit handling and FIFO processing of deferred CMD_SYNC writes
 *   when a submission crosses the end of the command ring.
 *
 * Method:
 *   Position the producer at the last slot, pause CMD_SYNC, then submit a
 *   page invalidation so its MSI CMD_SYNC lands in slot zero. Queue two more
 *   MSI writes carrying 1 and 2 to the same destination, each with a SEV
 *   CMD_SYNC. Inspect the paused state, resume and inspect the final state.
 *
 * Expected results:
 *   Submissions return 0. While paused, both destinations remain UINT32_MAX
 *   and the consumer stops at slot zero with the correct wrap bit. Resuming
 *   completes the original invalidation, leaves 2 in the later destination
 *   and consumes all seven commands in the submitted sequence.
 */
TEST(smmuv3_tlbi_active_psmmu, paused_cmd_sync_preserves_wrapped_queue_order)
{
	uint32_t entries = U(1) << smmu->config.cmdq_log2size;
	uint32_t mask = (entries << 1) - 1U;
	uint32_t start_prod;
	unsigned int vmid = 1U;

	CHECK_EQUAL(0, smmuv3_cmd_sync_init(&pending_sync, (uintptr_t)&pending_sync));
	/* Place the TLBI in the last slot and its deferred CMD_SYNC in slot zero. */
	while ((read32(smmu->cmdq.prod_reg) & (entries - 1U)) != (entries - 1U)) {
		/* Unpaused commands advance both indices without leaving work pending. */
		CHECK_EQUAL(0, prepare_send_command(smmu, CMD_SYNC, 0UL, 0UL));
	}
	start_prod = read32(smmu->cmdq.prod_reg);
	/* Hold the first CMD_SYNC as submission crosses the ring boundary. */
	CHECK_EQUAL(0, smmuv3_arch_pause_cmd_sync(smmu, true));
	/* Publishing the wrapped sequence must succeed while completion is held. */
	CHECK_EQUAL(0, smmuv3_inv_at_level_per_vmids_submit(&vmid, 1U,
				0UL, S2TT_PAGE_LEVEL, 1UL, true, &pending_sync));
	/* Queue a distinct value behind the stalled completion to track ordering. */
	CHECK_EQUAL(0, prepare_send_cmd_sync(smmu, (uintptr_t)&later_completion, 1U));
	/* A later write to the same word must eventually replace the first value. */
	CHECK_EQUAL(0, prepare_send_cmd_sync(smmu, (uintptr_t)&later_completion, 2U));
	/* Wrapping must not allow the first MSI to bypass the pause. */
	UNSIGNED_LONGS_EQUAL(UINT32_MAX, pending_sync.completion[TEST_HELPERS_SMMU_IDX]);
	/* Neither later MSI may overtake the stalled CMD_SYNC. */
	UNSIGNED_LONGS_EQUAL(UINT32_MAX, later_completion);
	/* The consumer must stop at slot zero with the correct wrap bit. */
	UNSIGNED_LONGS_EQUAL((start_prod + 1U) & mask, read32(smmu->cmdq.cons_reg));
	/* Release the pause and drain all queued writes in submission order. */
	CHECK_EQUAL(0, smmuv3_arch_pause_cmd_sync(smmu, false));
	/* The first MSI must clear the original invalidation's pending word. */
	CHECK_TRUE(smmuv3_cmd_sync_is_complete(&pending_sync));
	/* The final value must come from the second of the two later MSI writes. */
	UNSIGNED_LONGS_EQUAL(2U, later_completion);
	/* One TLBI, three MSI writes and three SEVs must all have been consumed. */
	UNSIGNED_LONGS_EQUAL(7UL, tlbi_test_smmu_command_count(smmu, start_prod));
}

/*
 * TC12: Skip explicit invalidation commands on a BTM PSMMU.
 *
 * Public APIs tested:
 *   smmuv3_inv(), smmuv3_inv_entries(), smmuv3_inv_at_level(),
 *   smmuv3_inv_at_level_per_vmids(), smmuv3_inv_at_level_per_vmids_submit(),
 *   smmuv3_cmd_sync_is_complete().
 *
 * Aim:
 *   Verify that invalidation APIs rely on broadcast maintenance for a BTM
 *   PSMMU while issuing commands to an active non-BTM PSMMU.
 *
 * Method:
 *   With both devices active, record their producer indices and exercise
 *   global, VMID, range and VMID-list invalidation, including asynchronous
 *   submission. Inspect completion state and both devices' command counts.
 *
 * Expected results:
 *   Every call returns 0 and the shared object reports complete after
 *   fake_host processing. The BTM completion word is zero and its queue has
 *   no new commands; the non-BTM queue has consumed commands.
 */
TEST(smmuv3_tlbi_active_psmmu, btm_psmmu_skips_explicit_tlbi)
{
	struct smmuv3_dev *btm_smmu = smmuv3_psmmu_find(host_util_get_smmu_ns_base(0U));
	struct smmuv3_cmd_sync sync = {};
	unsigned int vmids[] = {2U, 1U};
	uint32_t btm_start_prod = read32(btm_smmu->cmdq.prod_reg);
	uint32_t start_prod = read32(smmu->cmdq.prod_reg);

	/* Confirm the device under observation participates in broadcast TLBIs. */
	CHECK_TRUE((btm_smmu->config.features & FEAT_BTM) != 0U);
	CHECK_EQUAL(0, smmuv3_cmd_sync_init(&sync, (uintptr_t)&sync));
	/* Global invalidation must succeed with both types of device active. */
	CHECK_EQUAL(0, smmuv3_inv(&sync));
	/* Entry invalidation must also support the mixed BTM/non-BTM fixture. */
	CHECK_EQUAL(0, smmuv3_inv_entries(0U, vmids[0], &sync));
	/* The single-VMID range API must complete a page invalidation. */
	CHECK_EQUAL(0, smmuv3_inv_at_level(vmids[0], 0UL, 3L, 1UL, true, &sync));
	/* The synchronous list API must complete invalidations for both VMIDs. */
	CHECK_EQUAL(0, smmuv3_inv_at_level_per_vmids(vmids, ARRAY_SIZE(vmids),
						     0UL, 3L, 1UL, true, &sync));
	/* The asynchronous variant must accept the same request without polling. */
	CHECK_EQUAL(0, smmuv3_inv_at_level_per_vmids_submit(vmids, ARRAY_SIZE(vmids),
							    0UL, 3L, 1UL, true, &sync));
	/* Immediate fake_host processing must leave no outstanding completions. */
	CHECK_TRUE(smmuv3_cmd_sync_is_complete(&sync));
	/* The BTM device must have no pending software-command completion. */
	UNSIGNED_LONGS_EQUAL(0U, sync.completion[0]);
	/* None of the exercised APIs may enqueue an explicit TLBI on the BTM device. */
	UNSIGNED_LONGS_EQUAL(0UL, tlbi_test_smmu_command_count(btm_smmu, btm_start_prod));
	/* The non-BTM queue must advance, proving the requests were processed. */
	CHECK_TRUE(tlbi_test_smmu_command_count(smmu, start_prod) > 0UL);
}

/*
 * TC13: Initialize completion storage and reject invalid arguments.
 *
 * Public APIs tested:
 *   smmuv3_cmd_sync_init().
 *
 * Aim:
 *   Verify completion-array address calculation, clearing of stale pending
 *   state and validation of the CMD_SYNC object pointer and physical address.
 *
 * Method:
 *   Seed the first completion word with UINT32_MAX, initialize the object
 *   with its physical address, then inspect completion_pa and every word.
 *   Repeat initialization with a NULL object and with a zero physical address.
 *
 * Expected results:
 *   Valid initialization returns 0, sets completion_pa to the object's PA
 *   plus the completion member offset, and clears all per-SMMU words to zero.
 *   Both invalid argument cases return -EINVAL.
 */
TEST(smmuv3_tlbi, cmd_sync_init)
{
	struct smmuv3_cmd_sync cmd_sync = {};
	uintptr_t cmd_sync_pa = (uintptr_t)&cmd_sync;
	uintptr_t completion_pa = cmd_sync_pa +
				  offsetof(struct smmuv3_cmd_sync, completion);

	cmd_sync.completion[0] = UINT32_MAX;

	LONGS_EQUAL(0L, smmuv3_cmd_sync_init(&cmd_sync, cmd_sync_pa));
	/* MSI destinations must use the completion member's PA within the object. */
	UNSIGNED_LONGS_EQUAL((unsigned long)completion_pa,
			     (unsigned long)cmd_sync.completion_pa);
	for (unsigned int i = 0U; i < RMM_MAX_SMMUS; i++) {
		/* Every slot must start idle, including the stale pending slot. */
		UNSIGNED_LONGS_EQUAL(0U, cmd_sync.completion[i]);
	}

	/* Reject a missing CPU-accessible object even when its PA is nonzero. */
	LONGS_EQUAL(-EINVAL, smmuv3_cmd_sync_init(NULL, cmd_sync_pa));
	/* Reject a zero physical address even when the object pointer is valid. */
	LONGS_EQUAL(-EINVAL, smmuv3_cmd_sync_init(&cmd_sync, 0UL));
}

/*
 * TC14: Include the final SMMU slot in aggregate completion checks.
 *
 * Public APIs tested:
 *   smmuv3_cmd_sync_is_complete().
 *
 * Aim:
 *   Verify that completion detection includes the upper bound of the
 *   per-SMMU completion array.
 *
 * Method:
 *   Initialize an object and query completion with all words zero. Set only
 *   the final slot to the pending sentinel and query again, then clear that
 *   slot and perform a final query.
 *
 * Expected results:
 *   Initialization returns 0. The three completion queries return true,
 *   false and true, respectively.
 */
TEST(smmuv3_tlbi, cmd_sync_completion)
{
	struct smmuv3_cmd_sync cmd_sync = {};
	uintptr_t cmd_sync_pa = (uintptr_t)&cmd_sync;

	LONGS_EQUAL(0L, smmuv3_cmd_sync_init(&cmd_sync, cmd_sync_pa));
	/* With no submitted commands, all-zero words must report complete. */
	CHECK_TRUE(smmuv3_cmd_sync_is_complete(&cmd_sync));

	cmd_sync.completion[RMM_MAX_SMMUS - 1U] = U(-1);
	/* A pending final slot must prevent completion even if earlier slots are zero. */
	CHECK_FALSE(smmuv3_cmd_sync_is_complete(&cmd_sync));

	cmd_sync.completion[RMM_MAX_SMMUS - 1U] = 0U;
	/* Clearing the only pending word must restore aggregate completion. */
	CHECK_TRUE(smmuv3_cmd_sync_is_complete(&cmd_sync));
}

/*
 * TC15: Preserve the leaf bit at levels 0 and -1 without a TTL hint.
 *
 * Public APIs tested:
 *   smmuv3_inv_at_level().
 *
 * Aim:
 *   Verify LEAF and TTL in every generated TLBI for leaf requests at levels
 *   0 and -1, covering both one and multiple invalidation commands.
 *
 * Method:
 *   Submit one and 65 blocks at level 0 and one block at level -1 through
 *   smmuv3_inv_at_level() on the active non-BTM PSMMU with leaf=true.
 *   Inspect each TLBI's VMID, IPA, range coverage and hints. These ranges
 *   cannot produce a single-page command, so this does not exercise
 *   non-range encoding.
 *
 * Expected results:
 *   All calls succeed and cover each requested range exactly. Every TLBI has
 *   LEAF set, TTL zero and TG_4KB. Each request consumes one or two TLBIs
 *   followed by the MSI/SEV completion pair.
 */
TEST(smmuv3_tlbi_active_psmmu, levels_zero_and_minus_one_preserve_leaf)
{
	const struct {
		long level;
		unsigned long blocks;
		unsigned long commands;
	} cases[] = {
		{0L, 1UL, 1UL},
		{0L, 65UL, 2UL},
		{-1L, 1UL, 1UL}
	};
	struct smmuv3_cmd_sync sync = {};

	/* Initialize the MSI destinations used by synchronous invalidation. */
	CHECK_EQUAL(0, smmuv3_cmd_sync_init(&sync, (uintptr_t)&sync));
	for (unsigned int i = 0U; i < ARRAY_SIZE(cases); i++) {
		const unsigned long base = XLAT_BLOCK_SIZE(cases[i].level);
		const unsigned long block_granules = base / GRANULE_SIZE;
		uint32_t start_prod = read32(smmu->cmdq.prod_reg);
		unsigned long remaining = cases[i].blocks * block_granules;
		unsigned long next_ipa = base;

		CHECK_EQUAL(0, smmuv3_inv_at_level(2U, base, cases[i].level,
						 cases[i].blocks, true, &sync));
		CHECK_TRUE(smmuv3_cmd_sync_is_complete(&sync));
		/* All TLBIs in the request share one MSI/SEV completion pair. */
		UNSIGNED_LONGS_EQUAL(cases[i].commands + 2UL,
				     tlbi_test_smmu_command_count(smmu, start_prod));

		for (unsigned long j = 0UL; j < cases[i].commands; j++) {
			uint128_t cmd = tlbi_test_smmu_command(smmu, start_prod, j);
			uint64_t lo = (uint64_t)cmd;
			uint64_t hi = (uint64_t)(cmd >> 64);
			unsigned long covered = (EXTRACT(NUM, lo) + 1UL) << EXTRACT(SCALE, lo);

			/* Each range chunk must invalidate stage-2 translations by IPA. */
			UNSIGNED_LONGS_EQUAL(CMD_TLBI_S2_IPA, EXTRACT(CMD, lo));
			/* Range splitting must preserve the requested VMID. */
			UNSIGNED_LONGS_EQUAL(2UL, EXTRACT(VMID, lo));
			/* Chunks must be contiguous, with no gaps or overlap. */
			UNSIGNED_LONGS_EQUAL(next_ipa, hi & BIT_MASK_ULL(55U, 12U));
			/* Levels 0 and -1 have no TTL hint encoding for the 4KB granule. */
			UNSIGNED_LONGS_EQUAL(0UL, EXTRACT(TTL, hi));
			/* Multi-page ranges retain the 4KB granule encoding. */
			UNSIGNED_LONGS_EQUAL(TG_4KB, EXTRACT(TG, hi));
			/* Omitting TTL must preserve the caller's leaf-only request. */
			CHECK_TRUE((hi & LEAF_BIT) != 0UL);
			/* Each chunk must advance without overrunning the request. */
			CHECK_TRUE((covered > 0UL) && (covered <= remaining));
			next_ipa += covered * GRANULE_SIZE;
			remaining -= covered;
		}
		/* Together, the commands must cover every requested granule. */
		UNSIGNED_LONGS_EQUAL(0UL, remaining);
	}
}

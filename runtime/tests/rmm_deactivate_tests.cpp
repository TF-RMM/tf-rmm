/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/TestHarness.h>

extern "C" {
#include <dev_granule.h>
#include <glob_data.h>
#include <granule.h>
#include <host_rmi_wrappers.h>
#include <host_utils.h>
#include <platform_api.h>
#include <smc-handler.h>
#include <sro_context.h>
#include <status.h>
#include <test_helpers.h>
#include <tracking_region.h>
}

/* Return a range to NS, completing any coarse-granule undelegation SRO. */
static void undelegate_range(uintptr_t base, uintptr_t top)
{
	struct smc_result res = {};

	while (base < top) {
		unsigned long handle;
		unsigned int attempts = 0U;

		host_rmi_granule_range_undelegate((void *)base, (void *)top, &res);
		handle = res.x[1];
		while (unpack_return_code(res.x[0]).status == RMI_INCOMPLETE) {
			unsigned long call_handle = handle;
			unsigned long donate_req;

			CHECK_TRUE(attempts++ < 1024U);
			host_rmi_op_continue(&call_handle, 0UL, &donate_req, &res);
		}
		CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
		CHECK_TRUE((res.x[1] > base) && (res.x[1] <= top));
		base = res.x[1];
	}
}

/*
 * Exercise deactivation through the RMI dispatcher with an ACTIVE RMM, the
 * minimum tracking-region size and undelegated, fine-tracked memory. The
 * fixture supplies fine metadata independently of the boot configuration.
 * Teardown restores ACTIVE and the minimum region size after deactivation.
 */
TEST_GROUP(rmm_deactivate_tests) {
	/* Start with an ACTIVE RMM and undelegated fine-tracked memory. */
	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start(false);
		test_helpers_expect_assert_fail(false);
		test_helpers_allocate_reset();
		CHECK_EQUAL(0, host_util_set_default_sysreg_cb("isr_el1", 0UL));
		if (glob_data_get_rmm_state() == RMM_STATE_INIT) {
			CHECK_TRUE(glob_data_transition_rmm_state(RMM_STATE_INIT,
								RMM_STATE_ACTIVE));
		}
		CHECK_EQUAL(RMM_STATE_ACTIVE, glob_data_get_rmm_state());
	}

	/* Restore tracking after successful deactivation for the next test. */
	TEST_TEARDOWN()
	{
		struct smc_result res = {};

		CHECK_EQUAL(0, test_helpers_unregister_cb(CB_BUFFER_MAP));
		if (glob_data_get_rmm_state() == RMM_STATE_INIT) {
			CHECK_EQUAL(0, tracking_region_configure(TRACKING_REGION_MIN_SIZE));
			host_rmm_activate(&res);
			CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
		}
		CHECK_EQUAL(RMM_STATE_ACTIVE, glob_data_get_rmm_state());
	}
};

/*
 * Verify the architected FID and the lifecycle restrictions after deactivation.
 *
 * Setup: RMM is ACTIVE and all tracked granules are undelegated. Invoke
 * RMI_RMM_DEACTIVATE, probe commands in INIT, then reactivate and deactivate.
 *
 * Expected:
 *  - SMC_RMI_RMM_DEACTIVATE is 0xC400020F.
 *  - Deactivation returns RMI_SUCCESS, publishes INIT and clears x1-x3.
 *  - Granule delegation and another deactivation return RMI_ERROR_GLOBAL
 *    in INIT, while RMI_VERSION remains available.
 *  - Reactivation returns RMI_SUCCESS and restores ACTIVE; the following
 *    deactivation also succeeds.
 */
TEST(rmm_deactivate_tests, success_and_reactivation)
{
	struct smc_result res = {};
	uintptr_t addr = test_helpers_allocate_granules(1U);

	UNSIGNED_LONGS_EQUAL(0xC400020FUL, SMC_RMI_RMM_DEACTIVATE);
	host_rmm_deactivate(&res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(RMM_STATE_INIT, glob_data_get_rmm_state());
	CHECK_EQUAL(0UL, res.x[1]);
	CHECK_EQUAL(0UL, res.x[2]);
	CHECK_EQUAL(0UL, res.x[3]);

	host_rmi_granule_range_delegate((void *)addr,
				       (void *)(addr + GRANULE_SIZE), &res);
	CHECK_EQUAL(RMI_ERROR_GLOBAL, res.x[0]);
	host_rmm_deactivate(&res);
	CHECK_EQUAL(RMI_ERROR_GLOBAL, res.x[0]);
	host_rmi_version(MAKE_RMI_REVISION(2UL, 0UL), &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	host_rmm_activate(&res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(RMM_STATE_ACTIVE, glob_data_get_rmm_state());
	host_rmm_deactivate(&res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/*
 * Verify that both the dispatcher and handler reject invalid lifecycle states.
 *
 * Setup: With no delegated granules, force the RMM state to INIT and then
 * INTERMEDIATE. In each state, call through the host wrapper and directly
 * invoke smc_rmm_deactivate(). Restore ACTIVE before trying the next state.
 *
 * Expected: Both entry paths return RMI_ERROR_GLOBAL and leave the lifecycle
 * state unchanged. This isolates lifecycle validation from granule checks.
 */
TEST(rmm_deactivate_tests, invalid_lifecycle_states)
{
	const enum rmm_state states[] = {RMM_STATE_INIT, RMM_STATE_INTERMEDIATE};
	struct smc_result res = {};

	for (unsigned int i = 0U; i < ARRAY_SIZE(states); i++) {
		CHECK_TRUE(glob_data_transition_rmm_state(RMM_STATE_ACTIVE, states[i]));
		host_rmm_deactivate(&res);
		CHECK_EQUAL(RMI_ERROR_GLOBAL, res.x[0]);
		CHECK_EQUAL(states[i], glob_data_get_rmm_state());
		/* Direct callers must enforce the same state contract. */
		smc_rmm_deactivate(&res);
		CHECK_EQUAL(RMI_ERROR_GLOBAL, res.x[0]);
		CHECK_TRUE(glob_data_transition_rmm_state(states[i], RMM_STATE_ACTIVE));
	}
}

/*
 * Verify that deactivation checks fine conventional metadata to the bank's end.
 *
 * Setup: Set the last conventional granule to each listed non-NS state,
 * including INTERNAL, while all other granules remain NS. Attempt deactivation
 * for each state and restore the granule to NS between attempts.
 *
 * Expected: Each non-NS state causes RMI_ERROR_GLOBAL and leaves RMM ACTIVE.
 * Once the last granule is NS again, deactivation returns RMI_SUCCESS.
 */
TEST(rmm_deactivate_tests, fine_conventional_states)
{
	const unsigned char states[] = {
		GRANULE_STATE_DELEGATED, GRANULE_STATE_RD, GRANULE_STATE_REC,
		GRANULE_STATE_REC_AUX, GRANULE_STATE_DATA, GRANULE_STATE_RTT,
		GRANULE_STATE_PDEV, GRANULE_STATE_PDEV_AUX, GRANULE_STATE_VDEV,
		GRANULE_STATE_VDEV_AUX, GRANULE_STATE_PARTIAL,
		GRANULE_STATE_INTERNAL, GRANULE_STATE_RD_AUX
	};
	struct smc_result res = {};
	struct granule *g = tr_addr_to_granule(host_util_get_granule_base() +
		(test_helpers_get_nr_granules() - 1UL) * GRANULE_SIZE);

	for (unsigned int i = 0U; i < ARRAY_SIZE(states); i++) {
		granule_lock(g, GRANULE_STATE_NS);
		granule_unlock_transition(g, states[i]);
		host_rmm_deactivate(&res);
		CHECK_EQUAL(RMI_ERROR_GLOBAL, res.x[0]);
		CHECK_EQUAL(RMM_STATE_ACTIVE, glob_data_get_rmm_state());
		granule_lock(g, states[i]);
		granule_unlock_transition(g, GRANULE_STATE_NS);
	}
	host_rmm_deactivate(&res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/*
 * Verify that fine device metadata participates in deactivation validation.
 *
 * Setup: For each configured coherent and non-coherent device bank, set its
 * last granule to DELEGATED, MAPPED and PARTIAL in turn. Attempt deactivation
 * in each state, restoring NS afterwards. Coverage follows the platform's
 * available device banks and includes each bank's final granule.
 *
 * Expected: Each non-NS device state causes RMI_ERROR_GLOBAL and leaves RMM
 * ACTIVE. Deactivation returns RMI_SUCCESS after all device granules are NS.
 */
TEST(rmm_deactivate_tests, fine_device_states)
{
	const unsigned char states[] = {
		DEV_GRANULE_STATE_DELEGATED, DEV_GRANULE_STATE_MAPPED,
		DEV_GRANULE_STATE_PARTIAL
	};
	const unsigned long categories[] = {
		RMI_MEM_CATEGORY_DEV_NCOH, RMI_MEM_CATEGORY_DEV_COH
	};
	struct smc_result res = {};

	for (unsigned int cat = 0U; cat < ARRAY_SIZE(categories); cat++) {
		unsigned long count;
		const struct plat_memory_bank *banks = plat_get_mem_banks(categories[cat], &count);

		for (unsigned long bank = 0UL; bank < count; bank++) {
			enum dev_coh_type type;
			unsigned long size;
			uintptr_t addr = banks[bank].base + banks[bank].size - GRANULE_SIZE;
			struct dev_granule *g;

			CHECK_EQUAL(RMI_SUCCESS, tr_find_lock_active_dev_granule(addr,
				DEV_GRANULE_STATE_NS, &g, &type, &size));
			dev_granule_unlock(g);
			for (unsigned int i = 0U; i < ARRAY_SIZE(states); i++) {
				dev_granule_lock(g, DEV_GRANULE_STATE_NS);
				dev_granule_unlock_transition(g, states[i]);
				host_rmm_deactivate(&res);
				CHECK_EQUAL(RMI_ERROR_GLOBAL, res.x[0]);
				CHECK_EQUAL(RMM_STATE_ACTIVE, glob_data_get_rmm_state());
				dev_granule_lock(g, states[i]);
				dev_granule_unlock_transition(g, DEV_GRANULE_STATE_NS);
			}
		}
	}
	host_rmm_deactivate(&res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/*
 * Verify that validation uses active coarse metadata rather than stale fine
 * metadata that still describes the same memory as NS.
 *
 * Setup: In each conventional, coherent device and non-coherent device bank
 * containing a full aligned tracking region, switch that region to COARSE
 * and delegate it. Attempt deactivation, then undelegate the region, completing
 * any SRO. Banks without a full aligned region are not exercised.
 *
 * Expected: Each delegated coarse region causes RMI_ERROR_GLOBAL and leaves
 * RMM ACTIVE. Deactivation returns RMI_SUCCESS after every region is NS again.
 */
TEST(rmm_deactivate_tests, coarse_conventional_and_device_states)
{
	const unsigned long categories[] = {
		RMI_MEM_CATEGORY_CONVENTIONAL, RMI_MEM_CATEGORY_DEV_NCOH,
		RMI_MEM_CATEGORY_DEV_COH
	};
	struct smc_result res = {};

	for (unsigned int i = 0U; i < ARRAY_SIZE(categories); i++) {
		unsigned long count;
		const struct plat_memory_bank *banks = plat_get_mem_banks(categories[i], &count);
		unsigned long size = tracking_region_get_size();

		for (unsigned long bank = 0UL; bank < count; bank++) {
			uintptr_t base = banks[bank].base;

			/* Coarse tracking requires a full region without any holes. */
			base = round_up(base, size);
			if ((base + size) > (banks[bank].base + banks[bank].size)) {
				continue;
			}
			CHECK_EQUAL(RMI_SUCCESS, tracking_region_set_tracking(base,
				categories[i], RMI_TRACKING_COARSE));
			host_rmi_granule_range_delegate((void *)base, (void *)(base + size), &res);
			CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
			host_rmm_deactivate(&res);
			CHECK_EQUAL(RMI_ERROR_GLOBAL, res.x[0]);
			CHECK_EQUAL(RMM_STATE_ACTIVE, glob_data_get_rmm_state());
			undelegate_range(base, base + size);
		}
	}
	host_rmm_deactivate(&res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/*
 * Verify that a region without granule tracking does not block deactivation.
 *
 * Setup: Change an aligned conventional region from FINE to NONE while all
 * memory is undelegated, then invoke RMI_RMM_DEACTIVATE.
 *
 * Expected: RMI_SUCCESS. A NONE region has no delegated granules to validate
 * and can be discarded along with the remaining undelegated tracking layout.
 */
TEST(rmm_deactivate_tests, untracked_regions)
{
	struct smc_result res = {};
	uintptr_t base = round_up(host_util_get_granule_base(), tracking_region_get_size());

	CHECK_EQUAL(RMI_SUCCESS, tracking_region_set_tracking(base,
		RMI_MEM_CATEGORY_CONVENTIONAL, RMI_TRACKING_NONE));
	host_rmm_deactivate(&res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/*
 * Run in a separate test process to preserve the tracking backing supplied
 * by boot. Unlike the main fixture, leave RMM in INIT without populating
 * additional fine metadata or activating the tracking layout.
 */
TEST_GROUP(rmm_deactivate_boot_tests) {
	/* Use only boot-provided backing, including when fine allocation is disabled. */
	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start_for_tracking_sro(false);
		test_helpers_expect_assert_fail(false);
	}
};

/*
 * Verify that deactivation and reactivation work with boot-provided backing.
 *
 * Setup: Start in INIT using only the backing selected by the build, then
 * perform two activation/deactivation cycles. With RMM_ALLOC_TRACKING_DATA
 * disabled, this also exercises a layout without preallocated fine arrays.
 *
 * Expected: Every activation and deactivation returns RMI_SUCCESS, and each
 * deactivation leaves RMM in INIT so the retained backing can be reused.
 */
TEST(rmm_deactivate_boot_tests, boot_backing)
{
	struct smc_result res = {};

	for (unsigned int i = 0U; i < 2U; i++) {
		host_rmm_activate(&res);
		CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
		host_rmm_deactivate(&res);
		CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
		CHECK_EQUAL(RMM_STATE_INIT, glob_data_get_rmm_state());
	}
}

/*
 * Verify that an unfinished SRO blocks deactivation between RMI calls.
 *
 * Setup: Reserve and seal a granule-range delegation SRO without delegating
 * memory, then attempt deactivation. Find and release the sealed context
 * before retrying. No executing RMI or delegated granule masks the SRO check.
 *
 * Expected: The first attempt returns RMI_BUSY and leaves RMM ACTIVE; the
 * sealed context remains accessible by its handle. After releasing that
 * context, deactivation returns RMI_SUCCESS.
 */
TEST(rmm_deactivate_tests, pending_sro)
{
	struct smc_result res = {};
	unsigned long handle;

	CHECK_EQUAL(RMI_SUCCESS, sro_ctx_reserve(SMC_RMI_GRANULE_RANGE_DELEGATE,
		0UL, false, false, SMC_RMI_OP_CONTINUE));
	handle = sro_ctx_seal();
	host_rmm_deactivate(&res);
	CHECK_EQUAL(RMI_BUSY, res.x[0]);
	CHECK_EQUAL(RMM_STATE_ACTIVE, glob_data_get_rmm_state());
	CHECK_TRUE(sro_ctx_find(handle));
	sro_ctx_release();
	host_rmm_deactivate(&res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/* Attempt deactivation while CONFIG_GET is using a shared dispatch lock. */
static void *deactivate_during_buffer_map(unsigned int slot, unsigned long addr)
{
	struct smc_result res = {};

	host_rmm_deactivate(&res);
	CHECK_EQUAL(RMI_BUSY, res.x[0]);
	CHECK_EQUAL(RMM_STATE_ACTIVE, glob_data_get_rmm_state());
	return host_util_slot_map(slot, addr);
}

/*
 * Verify that an executing RMI prevents exclusive access for deactivation.
 *
 * Setup: Install a buffer-map callback that invokes RMI_RMM_DEACTIVATE from
 * inside RMI_RMM_CONFIG_GET, while CONFIG_GET holds the shared dispatch lock.
 * This models an in-flight call without requiring a second host thread.
 * Remove the callback after CONFIG_GET returns, then retry deactivation.
 *
 * Expected: The nested deactivation returns RMI_BUSY and leaves RMM ACTIVE.
 * CONFIG_GET completes with RMI_SUCCESS, and deactivation succeeds once the
 * outer call has released the dispatch lock.
 */
TEST(rmm_deactivate_tests, executing_rmi)
{
	struct smc_result res = {};
	union test_harness_cbs cb;

	cb.buffer_map = deactivate_during_buffer_map;
	CHECK_EQUAL(0, test_helpers_register_cb(cb, CB_BUFFER_MAP));
	host_rmi_rmm_config_get(test_helpers_allocate_granules(1U), &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(0, test_helpers_unregister_cb(CB_BUFFER_MAP));
	host_rmm_deactivate(&res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/*
 * Verify that deactivation permits changing tracking regions from 1GB to 2MB.
 *
 * Setup: Deactivate the fixture's initial layout. Configure 4KB granules and
 * 1GB tracking regions through RMI_RMM_CONFIG_SET, then activate and deactivate.
 * Repeat with 2MB tracking regions, using the build's normal tracking mode.
 *
 * Expected: Each RMI returns RMI_SUCCESS. Each activation publishes ACTIVE
 * with the requested tracking-region size, and each deactivation restores
 * INIT so the following configuration can rebuild the layout.
 */
TEST(rmm_deactivate_tests, reconfigure_1gb_to_2mb)
{
	const struct {
		unsigned long config_size;
		unsigned long size;
	} layouts[] = {
		{RMI_GRAN_4KB_TRACKING_REGION_SIZE_1GB, TRACKING_REGION_MAX_SIZE},
		{RMI_GRAN_4KB_TRACKING_REGION_SIZE_2MB, TRACKING_REGION_MIN_SIZE}
	};
	struct smc_result res = {};
	struct rmi_rmm_config *cfg = (struct rmi_rmm_config *)
					test_helpers_allocate_granules(1U);

	host_rmm_deactivate(&res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(RMM_STATE_INIT, glob_data_get_rmm_state());
	*cfg = {};
	cfg->rmi_granule_size = RMI_GRANULE_SIZE_4KB;
	for (unsigned int i = 0U; i < ARRAY_SIZE(layouts); i++) {
		cfg->tracking_region_size = layouts[i].config_size;
		host_rmi_rmm_config_set((uintptr_t)cfg, &res);
		CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
		CHECK_EQUAL(RMM_STATE_INIT, glob_data_get_rmm_state());
		host_rmm_activate(&res);
		CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
		CHECK_EQUAL(RMM_STATE_ACTIVE, glob_data_get_rmm_state());
		CHECK_EQUAL(layouts[i].size, tracking_region_get_size());
		host_rmm_deactivate(&res);
		CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
		CHECK_EQUAL(RMM_STATE_INIT, glob_data_get_rmm_state());
	}
}

/*
 * Verify that stale fine metadata neither blocks deactivation nor survives it.
 *
 * Setup: Delegate a full FINE conventional region, switch it to COARSE, then
 * undelegate the coarse region. The saved fine descriptor remains DELEGATED
 * even though the active coarse descriptor is NS. Deactivate, inspect the
 * saved descriptor, then reactivate and deactivate again.
 *
 * Expected: The stale fine descriptor is DELEGATED before deactivation and NS
 * afterwards. Both deactivations and the intervening activation return
 * RMI_SUCCESS, demonstrating that inactive metadata is cleared for reuse.
 */
TEST(rmm_deactivate_tests, inactive_fine_metadata)
{
	struct smc_result res = {};
	uintptr_t base = round_up(host_util_get_granule_base(), tracking_region_get_size());
	uintptr_t top = base + tracking_region_get_size();
	struct granule *fine = tr_addr_to_granule(base);

	host_rmi_granule_range_delegate((void *)base, (void *)top, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(RMI_SUCCESS, tracking_region_set_tracking(base,
		RMI_MEM_CATEGORY_CONVENTIONAL, RMI_TRACKING_COARSE));
	undelegate_range(base, top);
	CHECK_EQUAL(GRANULE_STATE_DELEGATED, granule_unlocked_state(fine));
	host_rmm_deactivate(&res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(GRANULE_STATE_NS, granule_unlocked_state(fine));
	host_rmm_activate(&res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	host_rmm_deactivate(&res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_features.h>
#include <arch_helpers.h>
#include <esr.h>
#include <exit.h>
#include <granule.h>
#include <host_utils.h>
#include <mec.h>
#include <rec.h>
#include <s2tt.h>
#include <smc-rmi.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
}

/*
 * Host-visible ESR field masks derived from DEN0137 beta2 A4.3.4.x / A4.3.10
 * and the corresponding ESR_EL2 ISS layouts in Arm ARM DDI0487L.b D24.2,
 * without reusing the implementation's aggregate masks under test.
 */
static constexpr unsigned long WFX_HOST_ESR_MASK =
	MASK(ESR_EL2_EC) | ESR_EL2_WFx_TI_BIT;

static constexpr unsigned long DATA_ABORT_HOST_COMMON_ESR_MASK =
	MASK(ESR_EL2_EC) |
	MASK(ESR_EL2_ABORT_SET) |
	ESR_EL2_ABORT_FNV_BIT |
	ESR_EL2_ABORT_EA_BIT |
	MASK(ESR_EL2_ABORT_FSC);

static constexpr unsigned long INSTRUCTION_ABORT_HOST_ESR_MASK =
	DATA_ABORT_HOST_COMMON_ESR_MASK & ~ESR_EL2_ABORT_FNV_BIT;

static constexpr unsigned long EMULATABLE_DATA_ABORT_HOST_ESR_MASK =
	DATA_ABORT_HOST_COMMON_ESR_MASK |
	ESR_EL2_ABORT_ISV_BIT |
	MASK(ESR_EL2_ABORT_SAS) |
	ESR_EL2_ABORT_SF_BIT |
	ESR_EL2_ABORT_WNR_BIT;

static constexpr unsigned long SYSREG_HOST_ESR_MASK =
	~MASK(ESR_EL2_SYSREG_TRAP_RT);

static constexpr unsigned long NONEMULATABLE_UNPROT_DATA_ABORT_HOST_ESR_MASK =
	DATA_ABORT_HOST_COMMON_ESR_MASK |
	MASK(ESR_EL2_IL) |
	ESR_EL2_ABORT_WNR_BIT;

static constexpr unsigned long SERROR_HOST_ESR_MASK =
	MASK(ESR_EL2_EC) |
	ESR_EL2_SERROR_IDS_BIT |
	MASK(ESR_EL2_SERROR_AET) |
	ESR_EL2_SERROR_EA_BIT |
	MASK(ESR_EL2_SERROR_DFSC);

struct exit_esr_test_context {
	struct rec rec;
	STRUCT_TYPE sysreg_state sysregs[1];
	struct rmi_rec_exit rec_exit;
};

static void init_syndrome_sysregs(void)
{
	LONGS_EQUAL(0, host_util_set_default_sysreg_cb((char *)"far_el2", 0UL));
	LONGS_EQUAL(0, host_util_set_default_sysreg_cb((char *)"hpfar_el2", 0UL));
	LONGS_EQUAL(0, host_util_set_default_sysreg_cb((char *)"par_el1", 0UL));
	LONGS_EQUAL(0, host_util_set_default_sysreg_cb((char *)"spsr_el2", 0UL));
}

static void init_context(struct exit_esr_test_context *ctx)
{
	(void)memset(ctx, 0, sizeof(*ctx));

	ctx->rec.active_plane_id = PLANE_0_ID;
	ctx->rec.gic_owner = PLANE_0_ID;
	ctx->rec.aux_data.sysregs = &ctx->sysregs[0];
	ctx->rec.realm_info.num_aux_planes = 0U;
	ctx->rec.realm_info.primary_s2_ctx.ipa_bits = GRANULE_SHIFT + 2U;
}

static unsigned long unprotected_ipa(void)
{
	return GRANULE_SIZE * 2UL;
}

static unsigned long different_unprotected_ipa(void)
{
	return unprotected_ipa() + GRANULE_SIZE;
}

static unsigned long hpfar_for_ipa(unsigned long ipa)
{
	/*
	 * Arm ARM DDI0487L.b D24.2.70 "HPFAR_EL2, Hypervisor IPA Fault Address
	 * Register": HPFAR_EL2.FIPA reports IPA bits [55:8], with the low bits
	 * implicitly zeroed to granule alignment.
	 */
	return ipa >> HPFAR_EL2_FIPA_OFFSET;
}

static unsigned long far_offset(unsigned long far)
{
	return far & ~GRANULE_MASK;
}

static void check_failed_stage1_replay_retries_realm(unsigned long ec)
{
	struct exit_esr_test_context ctx;
	unsigned long saved_par = PAR_EL1_F_BIT | 0x2468UL;
	unsigned long saved_mmfr3 = READ_CACHED_REG(id_aa64mmfr3_el1);
	unsigned long raw_esr = ec | ESR_EL2_ABORT_FSC_PERM_FAULT_START;

	/* Fake host does not implement 128-bit system register accesses. */
	WRITE_CACHED_REG(id_aa64mmfr3_el1, 0UL);

	init_context(&ctx);

	write_far_el2(unprotected_ipa());
	write_hpfar_el2(hpfar_for_ipa(different_unprotected_ipa()));
	write_par_el1(saved_par);
	write_esr_el2(raw_esr);

	CHECK_TRUE(handle_realm_exit(&ctx.rec, &ctx.rec_exit,
				     ARM_EXCEPTION_SYNC_LEL));
	WRITE_CACHED_REG(id_aa64mmfr3_el1, saved_mmfr3);
	UNSIGNED_LONGS_EQUAL(saved_par, read_par_el1());
}

/*
 * Audit map from unit-test names to the specification rules they exercise.
 *
 * Test name                                         RMM beta2 rule(s)       Arm ARM reference
 * wfx_exit_exposes_only_ec_and_ti                   A4.3.4.1 / RYQWST       D24.2 "ISS encoding for an exception from a WF* instruction"
 * sysreg_exit_clears_rt_from_esr                    A4.3.4.4 / RMZJRC       D24.2 "ISS encoding for an exception from MSR, MRS, or System instruction execution in AArch64 state",
 *                                                                              D24.2.41 "ESR_EL2, Exception Syndrome Register (EL2)"
 * serror_exit_preserves_ec_and_strips_iesb          A4.3.10 / RLRCFP        D24.2 "ISS encoding for an SError exception"
 * instruction_abort_exposes_only_sync_abort_fields  A4.3.4.2                D24.2 "ISS encoding for an exception from an Instruction Abort",
 *                                                                              D24.2.70 "HPFAR_EL2, Hypervisor IPA Fault Address Register"
 * emulatable_data_abort_strips_srt_sse_and_s1ptw    A4.3.4.3 / RRYVFL,      D24.2 "ISS encoding for an exception from a Data Abort",
 *                                                   XXHXJC, RFFNHW          D24.2.41 "ESR_EL2, Exception Syndrome Register (EL2)",
 *                                                                              D24.2.70 "HPFAR_EL2, Hypervisor IPA Fault Address Register"
 * nonemulatable_unprotected_data_abort_preserves_   A4.3.4.3 / DMTZMC,      D24.2 "ISS encoding for an exception from a Data Abort",
 * il_and_wnr                                        RRYVFL                  D24.2.41 "ESR_EL2, Exception Syndrome Register (EL2)",
 *                                                                              D24.2.70 "HPFAR_EL2, Hypervisor IPA Fault Address Register"
 * direct_permission_fault_uses_stage1_ipa           D1.3.2.1 / RFKLWR, D8.2.13
 */


TEST_GROUP(exit_esr_tests) {
	TEST_SETUP()
	{
		test_helpers_init();

		/* Enable the platform with support for multiple PEs. */
		test_helpers_rmm_start(true);

		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);

		init_syndrome_sysregs();
	}

	TEST_TEARDOWN()
	{}
};

TEST(exit_esr_tests, wfx_exit_exposes_only_ec_and_ti)
{
	/*
	 * DEN0137 beta2 A4.3.4.1 (RYQWST): on REC exit due to WFI/WFE, the host
	 * only gets ESR.EC and ISS.TI, with ISS.RN zeroed and all other exit
	 * fields zero. Arm ARM DDI0487L.b "ISS encoding for an exception from a
	 * WF* instruction" (D24-7422) defines the TI/RV/RN subfields, so this
	 * test injects extra ISS bits and checks that only TI survives.
	 */
	struct exit_esr_test_context ctx;
	unsigned long raw_esr = ESR_EL2_EC_WFX |
					MASK(ESR_EL2_IL) |
				ESR_EL2_WFx_TI_BIT |
				ESR_EL2_ABORT_SSE_BIT |
				ESR_EL2_ABORT_WNR_BIT;

	init_context(&ctx);

	write_elr_el2(0x1000UL);
	write_far_el2(0xfeedbeefUL);
	write_hpfar_el2(0x1234UL);
	write_esr_el2(raw_esr);

	CHECK_FALSE(handle_realm_exit(&ctx.rec, &ctx.rec_exit, ARM_EXCEPTION_SYNC_LEL));
	UNSIGNED_LONGS_EQUAL(RMI_EXIT_SYNC, ctx.rec_exit.exit_reason);
	UNSIGNED_LONGS_EQUAL(raw_esr & WFX_HOST_ESR_MASK, ctx.rec_exit.esr);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.far);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.hpfar);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.rtt_tree);
	UNSIGNED_LONGS_EQUAL(0x1004UL, read_elr_el2());
}

TEST(exit_esr_tests, sysreg_exit_clears_rt_from_esr)
{
	/*
	 * DEN0137 beta2 A4.3.4.4 (RMZJRC): on REC exit due to system register
	 * access, rec_exit.esr.ISS.RT is zero and the trapped register encoding
	 * fields are preserved from ESR_EL2. Arm ARM DDI0487L.b
	 * "ISS encoding for an exception from MSR, MRS, or System instruction
	 * execution in AArch64 state" (D24-7439) defines the trapped register
	 * fields carried in ISS, and "ESR_EL2, Exception Syndrome Register (EL2)"
	 * (D24.2.41) defines the enclosing ESR_EL2 layout.
	 */
	struct exit_esr_test_context ctx;
	unsigned long raw_esr = ESR_EL2_EC_SYSREG |
					MASK(ESR_EL2_IL) |
				ESR_EL2_SYSREG_DIRECTION |
				ESR_EL2_SYSREG_ICC_PMR_EL1 |
				INPLACE(ESR_EL2_SYSREG_TRAP_RT, 5UL);

	init_context(&ctx);

	write_elr_el2(0x2000UL);
	write_esr_el2(raw_esr);

	CHECK_FALSE(handle_realm_exit(&ctx.rec, &ctx.rec_exit, ARM_EXCEPTION_SYNC_LEL));
	UNSIGNED_LONGS_EQUAL(RMI_EXIT_SYNC, ctx.rec_exit.exit_reason);
	UNSIGNED_LONGS_EQUAL(raw_esr & SYSREG_HOST_ESR_MASK, ctx.rec_exit.esr);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & MASK(ESR_EL2_SYSREG_TRAP_RT));
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.far);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.hpfar);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.gprs[0]);
	UNSIGNED_LONGS_EQUAL(0x2004UL, read_elr_el2());
}

TEST(exit_esr_tests, serror_exit_preserves_ec_and_strips_iesb)
{
	/*
	 * DEN0137 beta2 A4.3.10 (RLRCFP): host-visible SError ESR preserves only
	 * EC, IDS, AET, EA, and DFSC. Arm ARM DDI0487L.b "ISS encoding for an
	 * SError exception" (D24-7463) defines IESB as a distinct ISS bit, so we
	 * set it in the raw syndrome and verify that RMM strips it before
	 * reporting the exit.
	 */
	struct exit_esr_test_context ctx;
	unsigned long raw_esr = ESR_EL2_EC_SERROR |
					ESR_EL2_SERROR_AET_UEO |
				ESR_EL2_SERROR_IESB_BIT |
				ESR_EL2_SERROR_EA_BIT |
				ESR_EL2_SERROR_DFSC_ASYNC;

	init_context(&ctx);

	write_far_el2(0x1111UL);
	write_hpfar_el2(0x2222UL);
	write_esr_el2(raw_esr);

	CHECK_FALSE(handle_realm_exit(&ctx.rec, &ctx.rec_exit, ARM_EXCEPTION_SERROR_LEL));
	UNSIGNED_LONGS_EQUAL(RMI_EXIT_SERROR, ctx.rec_exit.exit_reason);
	UNSIGNED_LONGS_EQUAL(raw_esr & SERROR_HOST_ESR_MASK, ctx.rec_exit.esr);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.far);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.hpfar);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & ESR_EL2_SERROR_IESB_BIT);
	UNSIGNED_LONGS_EQUAL(ESR_EL2_EC_SERROR, ctx.rec_exit.esr & MASK(ESR_EL2_EC));
}

TEST(exit_esr_tests, instruction_abort_exposes_only_sync_abort_fields)
{
	/*
	 * DEN0137 beta2 A4.3.4.2: once RMM reports an Instruction Abort to the
	 * host, rec_exit exposes only EC, ISS.SET, ISS.EA, ISS.IFSC, HPFAR, and
	 * the RTT tree index; all other exit fields are zero. Arm ARM
	 * DDI0487L.b "ISS encoding for an exception from an Instruction Abort"
	 * (D24-7445) defines the architected abort ISS bits such as FnV, EA,
	 * S1PTW, and IFSC. This test focuses on the host-facing sanitization rule,
	 * so it deliberately sets extra syndrome bits and checks that IL and
	 * S1PTW do not leak back to the host.
	 */
	struct exit_esr_test_context ctx;
	unsigned long raw_esr = ESR_EL2_EC_INST_ABORT |
					MASK(ESR_EL2_IL) |
				ESR_EL2_ABORT_SET_UEO |
				ESR_EL2_ABORT_FNV_BIT |
				ESR_EL2_ABORT_EA_BIT |
				ESR_EL2_ABORT_S1PTW_BIT |
				ESR_EL2_ABORT_FSC_SEA;

	init_context(&ctx);

	write_far_el2(0xdecafbadUL);
	write_hpfar_el2(0x1234UL);
	write_esr_el2(raw_esr);

	CHECK_FALSE(handle_realm_exit(&ctx.rec, &ctx.rec_exit, ARM_EXCEPTION_SYNC_LEL));
	UNSIGNED_LONGS_EQUAL(RMI_EXIT_SYNC, ctx.rec_exit.exit_reason);
	UNSIGNED_LONGS_EQUAL(raw_esr & INSTRUCTION_ABORT_HOST_ESR_MASK,
			     ctx.rec_exit.esr);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.far);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.hpfar);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.gprs[0]);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.rtt_tree);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & MASK(ESR_EL2_IL));
	UNSIGNED_LONGS_EQUAL(0UL,
		ctx.rec_exit.esr & ESR_EL2_ABORT_FNV_BIT);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & ESR_EL2_ABORT_S1PTW_BIT);
}

/*
 * DEN0137 A4.3.4.2 (RMGWRC): verify ESR sanitization on a normal
 * Instruction Abort REC exit. Set up an unassigned RAM entry in a level 1
 * root RTT and simulate a level 1 stage 2 translation fault at a Protected
 * IPA from Plane 0. This reaches handle_instruction_abort()'s final
 * reporting path after the external-abort and Realm-injection checks.
 *
 * FnV is architecturally RES0 for translation faults. Deliberately set it
 * in the synthetic syndrome, together with IL and S1PTW, to verify that
 * these fields are removed from the host-visible ESR. The expected mask
 * permits only EC, SET, EA and IFSC.
 *
 * Verify RMI_EXIT_SYNC, preservation of the fault IPA in HPFAR, and zero
 * FAR, gprs[0] and RTT tree index for the primary tree. Seed FAR_EL2 with
 * a nonzero address to detect accidental forwarding. The faulting PC must
 * remain unchanged so the instruction can be retried, and last_run_info
 * must retain the original ESR independently of Host-visible sanitization.
 */
TEST(exit_esr_tests, instruction_translation_fault_clears_fnv)
{
	struct exit_esr_test_context ctx;
	uintptr_t rtt_addr = test_helpers_allocate_granules(1U);
	unsigned long raw_hpfar = hpfar_for_ipa(GRANULE_SIZE);
	unsigned long raw_esr = ESR_EL2_EC_INST_ABORT |
				MASK(ESR_EL2_IL) |
				ESR_EL2_ABORT_FNV_BIT |
				ESR_EL2_ABORT_S1PTW_BIT |
				(ESR_EL2_ABORT_FSC_TRANSLATION_FAULT_L0 + 1UL);
	bool resume;

	init_context(&ctx);

	/* An unassigned RAM entry in a level 1 root RTT causes a REC exit. */
	struct s2tt_context *s2_ctx = &ctx.rec.realm_info.primary_s2_ctx;

	s2_ctx->ipa_bits = S2TT_MIN_IPA_BITS;
	s2_ctx->s2_starting_level = 1;
	s2_ctx->num_root_rtts = 1U;
	s2_ctx->mecid = MECID_SHARED;
	s2_ctx->g_rtt = find_granule(rtt_addr);
	CHECK_TRUE(s2_ctx->g_rtt != NULL);
	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_NS);
	s2tt_init_unassigned_ram(s2_ctx, (unsigned long *)rtt_addr, 0UL);
	granule_unlock_transition(s2_ctx->g_rtt, GRANULE_STATE_RTT);

	/* FnV is RES0 for translation faults; set it to test sanitization. */
	write_elr_el2(0x4000UL);
	write_far_el2(0xdecafbadUL);
	write_hpfar_el2(raw_hpfar);
	write_esr_el2(raw_esr);

	resume = handle_realm_exit(&ctx.rec, &ctx.rec_exit, ARM_EXCEPTION_SYNC_LEL);

	granule_lock(s2_ctx->g_rtt, GRANULE_STATE_RTT);
	(void)memset((void *)rtt_addr, 0, GRANULE_SIZE);
	granule_unlock_transition(s2_ctx->g_rtt, GRANULE_STATE_NS);

	CHECK_FALSE(resume);
	UNSIGNED_LONGS_EQUAL(RMI_EXIT_SYNC, ctx.rec_exit.exit_reason);
	UNSIGNED_LONGS_EQUAL(raw_esr & INSTRUCTION_ABORT_HOST_ESR_MASK,
			    ctx.rec_exit.esr);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & ESR_EL2_ABORT_FNV_BIT);
	UNSIGNED_LONGS_EQUAL(raw_hpfar, ctx.rec_exit.hpfar);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.far);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.gprs[0]);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.rtt_tree);
	UNSIGNED_LONGS_EQUAL(0x4000UL, read_elr_el2());
	UNSIGNED_LONGS_EQUAL(raw_esr, ctx.rec.plane[0].last_run_info.esr);
}

/*
 * DEN0137 A4.3.4.3 (RRYVFL): verify that a Data Abort REC exit preserves
 * FnV. Simulate a restartable Synchronous External Abort from Plane 0
 * using DFSC == SEA and SET == UEO. This exercises the Data Abort branch
 * of handle_sync_external_abort(), which must keep using the mask that
 * includes FnV when Instruction Abort reporting uses its dedicated mask.
 * Together with instruction_abort_exposes_only_sync_abort_fields, this
 * checks the distinct FnV treatment for both external-abort branches.
 *
 * Set FnV in the input syndrome and verify that the host-visible ESR
 * retains EC, SET, FnV, EA and DFSC. Include IL, S1PTW and WnR in the
 * synthetic syndrome to check that these fields are stripped on this
 * external-abort path.
 *
 * Verify RMI_EXIT_SYNC and zero FAR, HPFAR, gprs[0] and RTT tree index.
 * Seed FAR_EL2 and HPFAR_EL2 with nonzero values to detect accidental
 * forwarding. The faulting PC must remain unchanged so the restartable
 * abort can be retried on the next REC entry.
 */
TEST(exit_esr_tests, external_data_abort_preserves_fnv)
{
	struct exit_esr_test_context ctx;
	unsigned long raw_esr = ESR_EL2_EC_DATA_ABORT |
				MASK(ESR_EL2_IL) |
				ESR_EL2_ABORT_SET_UEO |
				ESR_EL2_ABORT_FNV_BIT |
				ESR_EL2_ABORT_EA_BIT |
				ESR_EL2_ABORT_S1PTW_BIT |
				ESR_EL2_ABORT_WNR_BIT |
				ESR_EL2_ABORT_FSC_SEA;

	init_context(&ctx);

	write_elr_el2(0x5000UL);
	write_far_el2(0xdecafbadUL);
	write_hpfar_el2(0x1234UL);
	write_esr_el2(raw_esr);

	CHECK_FALSE(handle_realm_exit(&ctx.rec, &ctx.rec_exit, ARM_EXCEPTION_SYNC_LEL));
	UNSIGNED_LONGS_EQUAL(RMI_EXIT_SYNC, ctx.rec_exit.exit_reason);
	UNSIGNED_LONGS_EQUAL(raw_esr & DATA_ABORT_HOST_COMMON_ESR_MASK,
			    ctx.rec_exit.esr);
	UNSIGNED_LONGS_EQUAL(ESR_EL2_ABORT_FNV_BIT,
			    ctx.rec_exit.esr & ESR_EL2_ABORT_FNV_BIT);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.far);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.hpfar);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.gprs[0]);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.rtt_tree);
	UNSIGNED_LONGS_EQUAL(0x5000UL, read_elr_el2());
}


TEST(exit_esr_tests, emulatable_data_abort_strips_srt_sse_and_s1ptw)
{
	/*
	 * DEN0137 beta2 A4.3.4.3 (RRYVFL, XXHXJC, RFFNHW): on an Emulatable Data
	 * Abort, the host gets the common abort fields plus ISV, SAS, SF, and
	 * WnR; ISS.SRT is zeroed, ISS.SSE is not propagated, FAR is reported with
	 * the granule offset only, and gprs[0] carries the write value. Arm ARM
	 * DDI0487L.b "ISS encoding for an exception from a Data Abort"
	 * (D24-7449) defines ISV/SAS/SSE/SRT/SF/FnV/WnR/DFSC, while
	 * D24.2.70 HPFAR_EL2 defines the IPA reporting consumed by rec_exit.hpfar.
	 */
	struct exit_esr_test_context ctx;
	unsigned int rt = 17U;
	unsigned long raw_far = (GRANULE_SIZE * 3UL) + 0x3cUL;
	unsigned long raw_hpfar = hpfar_for_ipa(unprotected_ipa());
	unsigned long raw_esr = ESR_EL2_EC_DATA_ABORT |
				MASK(ESR_EL2_IL) |
				ESR_EL2_ABORT_ISV_BIT |
				INPLACE(ESR_EL2_ABORT_SAS, ESR_EL2_ABORT_SAS_WORD_VAL) |
				ESR_EL2_ABORT_SSE_BIT |
				INPLACE(ESR_EL2_ABORT_SRT, rt) |
				ESR_EL2_ABORT_SET_UEO |
				ESR_EL2_ABORT_SF_BIT |
				ESR_EL2_ABORT_FNV_BIT |
				ESR_EL2_ABORT_EA_BIT |
				ESR_EL2_ABORT_S1PTW_BIT |
				ESR_EL2_ABORT_WNR_BIT |
				ESR_EL2_ABORT_FSC_TRANSLATION_FAULT_L0;

	init_context(&ctx);
	ctx.rec.plane[0].regs[rt] = 0x1122334455667788UL;

	write_spsr_el2(0UL);
	write_far_el2(raw_far);
	write_hpfar_el2(raw_hpfar);
	write_par_el1(different_unprotected_ipa());
	write_esr_el2(raw_esr);

	CHECK_FALSE(handle_realm_exit(&ctx.rec, &ctx.rec_exit, ARM_EXCEPTION_SYNC_LEL));
	UNSIGNED_LONGS_EQUAL(RMI_EXIT_SYNC, ctx.rec_exit.exit_reason);
	UNSIGNED_LONGS_EQUAL(raw_esr & EMULATABLE_DATA_ABORT_HOST_ESR_MASK,
			     ctx.rec_exit.esr);
	UNSIGNED_LONGS_EQUAL(far_offset(raw_far), ctx.rec_exit.far);
	UNSIGNED_LONGS_EQUAL(raw_hpfar, ctx.rec_exit.hpfar);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.rtt_tree);
	UNSIGNED_LONGS_EQUAL(ctx.rec.plane[0].regs[rt] & access_mask(raw_esr),
			     ctx.rec_exit.gprs[0]);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & ESR_EL2_ABORT_SSE_BIT);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & MASK(ESR_EL2_ABORT_SRT));
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & ESR_EL2_ABORT_S1PTW_BIT);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & MASK(ESR_EL2_IL));
}

TEST(exit_esr_tests, nonemulatable_unprotected_data_abort_preserves_il_and_wnr)
{
	/*
	 * DEN0137 beta2 A4.3.4.3 (DMTZMC, RRYVFL): on a Non-emulatable Data Abort
	 * at an Unprotected IPA, the host gets the common abort fields plus IL and
	 * WnR, while the other emulation-specific ISS fields remain zero. Arm ARM
	 * DDI0487L.b "ISS encoding for an exception from a Data Abort"
	 * (D24-7449) defines which bits live in ISS, while "ESR_EL2, Exception
	 * Syndrome Register (EL2)" (D24.2.41) defines IL outside ISS.
	 */
	struct exit_esr_test_context ctx;
	unsigned long raw_hpfar = hpfar_for_ipa(unprotected_ipa());
	unsigned long raw_esr = ESR_EL2_EC_DATA_ABORT |
				MASK(ESR_EL2_IL) |
				INPLACE(ESR_EL2_ABORT_SAS, ESR_EL2_ABORT_SAS_DWORD_VAL) |
				ESR_EL2_ABORT_SSE_BIT |
				INPLACE(ESR_EL2_ABORT_SRT, 9UL) |
				ESR_EL2_ABORT_SET_UEO |
				ESR_EL2_ABORT_SF_BIT |
				ESR_EL2_ABORT_FNV_BIT |
				ESR_EL2_ABORT_EA_BIT |
				ESR_EL2_ABORT_S1PTW_BIT |
				ESR_EL2_ABORT_WNR_BIT |
				ESR_EL2_ABORT_FSC_TRANSLATION_FAULT_L0;

	init_context(&ctx);

	write_spsr_el2(0UL);
	write_far_el2((GRANULE_SIZE * 5UL) + 0x44UL);
	write_hpfar_el2(raw_hpfar);
	write_par_el1(different_unprotected_ipa());
	write_esr_el2(raw_esr);

	CHECK_FALSE(handle_realm_exit(&ctx.rec, &ctx.rec_exit, ARM_EXCEPTION_SYNC_LEL));
	UNSIGNED_LONGS_EQUAL(RMI_EXIT_SYNC, ctx.rec_exit.exit_reason);
	UNSIGNED_LONGS_EQUAL(raw_esr & NONEMULATABLE_UNPROT_DATA_ABORT_HOST_ESR_MASK,
			     ctx.rec_exit.esr);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.far);
	UNSIGNED_LONGS_EQUAL(raw_hpfar, ctx.rec_exit.hpfar);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.gprs[0]);
	UNSIGNED_LONGS_EQUAL(MASK(ESR_EL2_IL), ctx.rec_exit.esr & MASK(ESR_EL2_IL));
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & ESR_EL2_ABORT_ISV_BIT);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & MASK(ESR_EL2_ABORT_SAS));
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & ESR_EL2_ABORT_SSE_BIT);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & MASK(ESR_EL2_ABORT_SRT));
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & ESR_EL2_ABORT_S1PTW_BIT);
	UNSIGNED_LONGS_EQUAL(ESR_EL2_ABORT_WNR_BIT,
			     ctx.rec_exit.esr & ESR_EL2_ABORT_WNR_BIT);
}

/*
 * Inject a direct stage 2 Data Abort permission fault with S1PTW clear.
 * Seed HPFAR_EL2 with a stale IPA and provide a different, successful
 * stage 1 translation result in PAR_EL1 for the faulting FAR_EL2 address.
 * Direct permission faults leave HPFAR_EL2 UNKNOWN, so the exit handler
 * must reconstruct the fault IPA using stage 1 translation replay.
 *
 * Verify RMI_EXIT_SYNC and HPFAR encoded from the translated IPA. Distinct
 * input addresses catch accidental reuse of the stale HPFAR_EL2 value.
 * Also verify that PAR_EL1 retains its saved value after replay. The test
 * temporarily disables D128 because the fake host supports only 64-bit
 * system register accesses. See the permission-fault references in the
 * audit map above.
 */
TEST(exit_esr_tests, direct_permission_fault_uses_stage1_ipa)
{
	struct exit_esr_test_context ctx;
	unsigned long fipa = unprotected_ipa();
	unsigned long stale_hpfar = hpfar_for_ipa(different_unprotected_ipa());
	unsigned long saved_mmfr3 = READ_CACHED_REG(id_aa64mmfr3_el1);
	unsigned long raw_esr = ESR_EL2_EC_DATA_ABORT |
				ESR_EL2_ABORT_FSC_PERM_FAULT_START;

	/* Direct stage 2 permission faults leave HPFAR_EL2 UNKNOWN. */
	/* Fake host does not implement 128-bit system register accesses. */
	WRITE_CACHED_REG(id_aa64mmfr3_el1, 0UL);

	init_context(&ctx);

	write_spsr_el2(0UL);
	write_far_el2(fipa + 0x44UL);
	write_hpfar_el2(stale_hpfar);
	write_par_el1(fipa);
	write_esr_el2(raw_esr);

	CHECK_FALSE(handle_realm_exit(&ctx.rec, &ctx.rec_exit, ARM_EXCEPTION_SYNC_LEL));
	WRITE_CACHED_REG(id_aa64mmfr3_el1, saved_mmfr3);
	UNSIGNED_LONGS_EQUAL(RMI_EXIT_SYNC, ctx.rec_exit.exit_reason);
	UNSIGNED_LONGS_EQUAL(hpfar_for_ipa(fipa), ctx.rec_exit.hpfar);
	UNSIGNED_LONGS_EQUAL(fipa, read_par_el1());
}

/*
 * Inject a direct stage 2 Data Abort permission fault and make the stage 1
 * translation replay fail by setting PAR_EL1.F. The helper supplies a
 * stale HPFAR_EL2 and disables D128 to use the fake host's 64-bit register
 * path. This models a stage 1 mapping that no longer translates when RMM
 * tries to recover the fault IPA.
 *
 * Verify that handle_realm_exit() requests a Realm retry and preserves the
 * saved PAR_EL1 value, including its failure bit. This checks that failed
 * IPA recovery takes the retry path without corrupting Realm PAR state.
 */
TEST(exit_esr_tests, failed_data_stage1_replay_retries_realm)
{
	check_failed_stage1_replay_retries_realm(ESR_EL2_EC_DATA_ABORT);
}

/*
 * Inject a direct stage 2 Instruction Abort permission fault and make the
 * stage 1 translation replay fail by setting PAR_EL1.F. The helper seeds
 * a stale HPFAR_EL2 and uses the fake host's 64-bit register path with
 * D128 disabled, exercising failed IPA recovery for an instruction fetch.
 *
 * Verify that handle_realm_exit() requests a Realm retry and preserves the
 * complete saved PAR_EL1 value. This covers the Instruction Abort caller
 * of the replay helper as well as restoration of Realm translation state
 * when the replay cannot provide a usable IPA.
 */
TEST(exit_esr_tests, failed_instruction_stage1_replay_retries_realm)
{
	check_failed_stage1_replay_retries_realm(ESR_EL2_EC_INST_ABORT);
}

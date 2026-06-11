/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_helpers.h>
#include <esr.h>
#include <exit.h>
#include <host_utils.h>
#include <rec.h>
#include <smc-rmi.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
}

namespace {

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
	DATA_ABORT_HOST_COMMON_ESR_MASK;

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
	MASK(ESR_EL2_IL);

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
 * il_only                                           RRYVFL                  D24.2.41 "ESR_EL2, Exception Syndrome Register (EL2)",
 *                                                                              D24.2.70 "HPFAR_EL2, Hypervisor IPA Fault Address Register"
 */

} /* namespace */

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
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & ESR_EL2_ABORT_S1PTW_BIT);
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

TEST(exit_esr_tests, nonemulatable_unprotected_data_abort_preserves_il_only)
{
	/*
	 * DEN0137 beta2 A4.3.4.3 (DMTZMC, RRYVFL): on a Non-emulatable Data Abort
	 * at an Unprotected IPA, the host gets the common abort fields plus IL,
	 * and all of the emulation-specific ISS fields remain zero. Arm ARM
	 * DDI0487L.b "ISS encoding for an exception from a Data Abort"
	 * (D24-7449) defines which bits live in ISS, while "ESR_EL2, Exception
	 * Syndrome Register (EL2)" (D24.2.41) defines IL outside ISS. This is the
	 * rule commit 36c3893f specifically fixed.
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
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & ESR_EL2_ABORT_WNR_BIT);
}

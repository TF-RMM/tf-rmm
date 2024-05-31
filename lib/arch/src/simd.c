/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <arch_helpers.h>
#include <assert.h>
#include <cpuid.h>
#include <simd.h>
#include <simd_private.h>
#include <string.h>

/* Contains CPU SIMD configuration discovered during init */
static struct simd_config g_simd_cfg = { 0 };

/* Set when SIMD init is completed during boot */
static bool g_simd_init_done;

/*
 * Per-CPU flag to track if CPU's SIMD registers are saved in memory. This
 * allows checks to figure out whether it is OK to use SIMD registers for RMM's
 * own purposes at R-EL2.
 */
static bool g_simd_state_saved[MAX_CPUS];

#define simd_has_sve(sc)	(((sc)->tflags & SIMD_TFLAG_SVE) != 0U)
#define simd_has_sme(sc)	(((sc)->tflags & SIMD_TFLAG_SME) != 0U)

#define is_ctx_init_done(sc)	(((sc)->sflags & SIMD_SFLAG_INIT_DONE) != 0U)
#define is_ctx_saved(sc)	(((sc)->sflags & SIMD_SFLAG_SAVED) != 0U)
#define is_ctx_sve_hint_set(sc)	(((sc)->sflags & SIMD_SFLAG_SVE_HINT) != 0U)

/* Check whether the SVE is being used in Streaming mode */
#define is_sve_mode_streaming(sc)	(simd_has_sme(sc) && is_sme_sm())

/*
 * Check whether SVE is being used in normal (non-streaming) mode by the
 * context. The SVE hint bit is not set which implies that the full normal SVE
 * register context is in use.
 *
 * If the context has SME then CPU must not be in Streaming SVE mode, so an
 * explicit check !is_sve_mode_streaming() is done.
 */
#define is_sve_mode_normal(sc)		(simd_has_sve(sc) &&		\
					 !is_ctx_sve_hint_set(sc) &&	\
					 !is_sve_mode_streaming(sc))

/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
void simd_reset(void)
{
	g_simd_init_done = false;
	(void)memset(&g_simd_cfg, 0, sizeof(struct simd_config));

	for (unsigned int i = 0U; i < MAX_CPUS; i++) {
		g_simd_state_saved[i] = false;
	}
}

/*
 * Returns 'true' if the current CPU's SIMD (FPU/SVE) live state is saved in
 * memory else 'false'.
 */
bool simd_is_state_saved(void)
{
	return g_simd_state_saved[my_cpuid()];
}

static void save_simd_ns_el2_config(struct simd_context *ctx,
				    struct simd_el2_regs *el2_regs)
{
	if (simd_has_sve(ctx)) {
		el2_regs->zcr_el2 = read_zcr_el2();
	}
}

static void restore_simd_el2_config(struct simd_context *ctx,
				    struct simd_el2_regs *el2_regs)
{
	if (simd_has_sve(ctx)) {
		if (read_zcr_el2() != el2_regs->zcr_el2) {
			write_zcr_el2(el2_regs->zcr_el2);
			isb();
		}
	}
}

static void save_simd_context(struct simd_context *ctx)
{
	/*
	 * Restore EL2 config registers of this context before saving vector
	 * registers.
	 */
	restore_simd_el2_config(ctx, &ctx->el2_regs);

	/*
	 * For SME, save the Streaming Vector Control Register that contains CPU
	 * global PSTATE.SM and PSTATE.ZA mode bits before saving the context.
	 */
	if (simd_has_sme(ctx)) {
		ctx->svcr = read_svcr();
	}

	/* Save SVE vector registers for normal or streaming SVE mode */
	if (is_sve_mode_normal(ctx) || is_sve_mode_streaming(ctx)) {
		bool include_ffr;

		if (is_sve_mode_streaming(ctx)) {
			include_ffr = sme_feat_fa64_enabled();
		} else {
			include_ffr = true;
		}

		/* Saving SVE Z registers emcompasses FPU Q registers */
		sve_save_vector_registers(&ctx->vregs.sve, include_ffr);
	} else {
		/* Save FPU Q registers */
		fpu_save_registers(&ctx->vregs.fpu);
	}

	/* Save ctl_status_regs */
	if (simd_has_sve(ctx)) {
		ctx->ctl_status_regs.zcr_el12 = read_zcr_el12();
	}
	ctx->ctl_status_regs.fpsr = read_fpsr();
	ctx->ctl_status_regs.fpcr = read_fpcr();

	/*
	 * Exit streaming mode after saving context by setting PSTATE.SM to 0.
	 * This will set each implemented bit of SVE registers Z0-Z31, P0-P15,
	 * and FFR to zero. Even if Normal SVE implements a  greater vector
	 * length than Streaming SVE, always the whole state is cleared.
	 *
	 * Exiting Streaming SVE mode doesn't have any impact on SME ZA storage
	 * or, if implemented, ZT0 storage.
	 */
	if (is_sve_mode_streaming(ctx)) {
		write_svcr(ctx->svcr & ~SVCR_SM_BIT);
		isb();
	}
}

static void restore_simd_context(struct simd_context *ctx)
{
	/*
	 * Restore EL2 config registers of this context before restoring vector
	 * registers.
	 */
	restore_simd_el2_config(ctx, &ctx->el2_regs);

	/*
	 * For SME, restore the Streaming Vector Control Register that contains
	 * CPU global PSTATE.SM and PSTATE.ZA mode bits before restoring the
	 * context.
	 *
	 * If PSTATE.SM is set to 1, then CPU enters Streaming SVE mode and each
	 * implemented bit of SVE registers Z0-Z31, P0-P15, and FFR in the new
	 * mode is set to zero. Even if Normal SVE implements a  greater vector
	 * length than Streaming SVE, always the whole state is cleared.
	 *
	 * Entering Streaming SVE mode doesn't have any impact on SME ZA storage
	 * or, if implemented, ZT0 storage.
	 */
	if (simd_has_sme(ctx)) {
		write_svcr(ctx->svcr);
		isb();
	}

	/* Restore SVE vector registers for normal or streaming SVE mode */
	if (is_sve_mode_normal(ctx) || is_sve_mode_streaming(ctx)) {
		bool include_ffr;

		if (is_sve_mode_streaming(ctx)) {
			include_ffr = sme_feat_fa64_enabled();
		} else {
			include_ffr = true;
		}

		/* Restoring SVE Z registers emcompasses FPU Q registers */
		sve_restore_vector_registers(&ctx->vregs.sve, include_ffr);
	} else {
		/* Restore FPU Q registers */
		fpu_restore_registers(&ctx->vregs.fpu);

		/*
		 * If the context has SVE and if SVE hint is set, restoring
		 * the Q[0-31] registers will clear all the upper bits of
		 * Z[0-31] registers. This will clear the contents of Z registers
		 * if the previous user was using SVE. But the P and FFR
		 * registers will hold the values from previous usage. So these
		 * registers have to be explicitly cleared.
		 */
		if (simd_has_sve(ctx)) {
			sve_clear_p_ffr_registers();
		}
	}

	/* Restore ctl_status_regs */
	if (simd_has_sve(ctx)) {
		write_zcr_el12(ctx->ctl_status_regs.zcr_el12);
	}
	write_fpsr(ctx->ctl_status_regs.fpsr);
	write_fpcr(ctx->ctl_status_regs.fpcr);
}

/*
 * Switches the SIMD context by saving the incoming context 'ctx_save' and
 * restoring the outgoing context 'ctx_restore'. It is possible to just have only
 * save or restore operation if the corresponding param is NULL. Returns the
 * SIMD context that is restored or if nothing is restored, returns NULL.
 */
struct simd_context *simd_context_switch(struct simd_context *ctx_save,
					 struct simd_context *ctx_restore)
{
	unsigned long rmm_cptr_el2;

	assert((ctx_save != NULL) || (ctx_restore != NULL));

	rmm_cptr_el2 = read_cptr_el2();

	/* Save tne incoming simd context */
	if (ctx_save != NULL) {
		assert(is_ctx_init_done(ctx_save));
		assert(!is_ctx_saved(ctx_save));
		assert(!g_simd_state_saved[my_cpuid()]);

		/*
		 * Disable appropriate traps. RMM core must run with SIMD traps
		 * enabled.
		 */
		write_cptr_el2(ctx_save->cptr_el2);
		isb();

		/*
		 * If incoming context belongs to NS world, then save NS world
		 * EL2 config registers. RMM saves these registers as EL3 may
		 * not save it as part of world switch.
		 */
		if (ctx_save->owner == SIMD_OWNER_NWD) {
			save_simd_ns_el2_config(ctx_save,
						&ctx_save->ns_el2_regs);
		}

		save_simd_context(ctx_save);

		ctx_save->sflags |= SIMD_SFLAG_SAVED;
		g_simd_state_saved[my_cpuid()] = true;
	}

	/* Restore the outgoing context */
	if (ctx_restore != NULL) {
		assert(is_ctx_init_done(ctx_restore));
		assert(is_ctx_saved(ctx_restore));
		assert(g_simd_state_saved[my_cpuid()]);

		/* Disable appropriate traps */
		if (read_cptr_el2() != ctx_restore->cptr_el2) {
			write_cptr_el2(ctx_restore->cptr_el2);
			isb();
		}

		restore_simd_context(ctx_restore);

		/*
		 * If outgoing context belongs to NS world, then restore NS
		 * world EL2 config registers. RMM saves these registers as EL3
		 * may not save it as part of world switch.
		 */
		if (ctx_restore->owner == SIMD_OWNER_NWD) {
			restore_simd_el2_config(ctx_restore,
						&ctx_restore->ns_el2_regs);
		}

		ctx_restore->sflags &= ~SIMD_SFLAG_SAVED;
		g_simd_state_saved[my_cpuid()] = false;
	}

	/* Restore traps */
	write_cptr_el2(rmm_cptr_el2);
	isb();

	return ctx_restore;
}

/*
 * Validate SIMD configurations are valid against with CPU SIMD configuration
 * discovered during init.
 */
static int validate_simd_config(const struct simd_config *simd_cfg)
{
	if (simd_cfg->sve_en) {
		if (!g_simd_cfg.sve_en ||
		    (simd_cfg->sve_vq > g_simd_cfg.sve_vq)) {
			return -1;
		}
	}

	if (simd_cfg->sme_en && !g_simd_cfg.sme_en) {
		return -1;
	}

	return 0;
}

/*
 * Verifies SIMD configuration and initializes SIMD context. Need to be only
 * done once per context. Can be invoked after simd_init().
 *
 * Parameters in:
 *	owner		- Owner of this SIMD context
 *	simd_cfg	- SIMD configurations
 *
 * Parameters out:
 *	simd_ctx	- Initializes 'simd_ctx' based on the 'simd_cfg'
 *
 * Returns:
 *	0		- on success
 *	-1		- on error
 */
int simd_context_init(simd_owner_t owner, struct simd_context *simd_ctx,
		      const struct simd_config *simd_cfg)
{
	if (!g_simd_init_done || is_ctx_init_done(simd_ctx)) {
		return -1;
	}

	if ((owner != SIMD_OWNER_REL1) && (owner != SIMD_OWNER_NWD)) {
		return -1;
	}

	/* Check whether SIMD configs are valid */
	if (validate_simd_config(simd_cfg) != 0) {
		return -1;
	}

	/*
	 * TODO: bzero SIMD context. Currently the SIMD context is assumed to be
	 * zeroed out but with FEAT_MEC enabled, the SIMD context in AUX granule
	 * might not be zeroed out.
	 */

	simd_ctx->owner = owner;

	/*
	 * REL1 SIMD context uses lazy enablement. The Realm SIMD context is
	 * considered to be saved as part of initialization. We need to restore
	 * this context when enabling SIMD for Realm.
	 */
	if (owner == SIMD_OWNER_REL1) {
		simd_ctx->sflags |= SIMD_SFLAG_SAVED;
	} else {
		simd_ctx->sflags &= ~SIMD_SFLAG_SAVED;
	}

	/* Construct the cptr_el2 for this context */
	simd_ctx->cptr_el2 = CPTR_EL2_VHE_INIT;
	SIMD_ENABLE_CPTR_FLAGS(simd_cfg, simd_ctx->cptr_el2);

	/* Initialize SVE related fields and config registers */
	if (simd_cfg->sve_en) {
		simd_ctx->tflags |= SIMD_TFLAG_SVE;

		simd_ctx->el2_regs.zcr_el2 = 0UL;
		simd_ctx->el2_regs.zcr_el2 |= INPLACE(ZCR_EL2_LEN,
						      simd_cfg->sve_vq);
	}

	/* Initialize SME related fields */
	if (simd_cfg->sme_en) {
		simd_ctx->tflags |= SIMD_TFLAG_SME;
		simd_ctx->svcr = 0UL;
	}

	simd_ctx->sflags |= SIMD_SFLAG_INIT_DONE;

	return 0;
}

/* Set or clear SVE hint bit passed by SMCCCv1.3 to SIMD context status */
void simd_update_smc_sve_hint(struct simd_context *ctx, bool sve_hint)
{
	assert(is_ctx_init_done(ctx));

	if (simd_has_sve(ctx)) {
		assert(!is_ctx_saved(ctx));
		if (sve_hint) {
			ctx->sflags |= SIMD_SFLAG_SVE_HINT;
		} else {
			ctx->sflags &= ~SIMD_SFLAG_SVE_HINT;
		}
	}
}

/* Returns CPU SIMD configuration discovered during init */
int simd_get_cpu_config(struct simd_config *simd_cfg)
{
	if (!g_simd_init_done) {
		return -1;
	}

	assert(simd_cfg != NULL);
	*simd_cfg = g_simd_cfg;

	return 0;
}

/*
 * Find the SVE max vector length restricted by EL3 and update the SVE specific
 * fields of global CPU SIMD config.
 */
static void sve_init_once(void)
{
	uint32_t sve_max_vq;
	unsigned long cptr_new, cptr_saved;

	cptr_saved = read_cptr_el2();

	/* Enable access to FPU and SVE */
	cptr_new = cptr_saved
		| INPLACE(CPTR_EL2_VHE_FPEN, CPTR_EL2_VHE_FPEN_NO_TRAP_11)
		| INPLACE(CPTR_EL2_VHE_ZEN, CPTR_EL2_VHE_ZEN_NO_TRAP_11);
	write_cptr_el2(cptr_new);
	isb();

	/*
	 * Write architecture max limit for vector length to ZCR_EL2.LEN and read
	 * back the sve vector length reported by rdvl. This will give the vector
	 * length limit set by EL3 for its lower ELs. RMM will use this value as
	 * max limit for EL2 and lower ELs.
	 *
	 * Configure ZCR.LEN to SVE_VQ_ARCH_MAX, the old zcr_el2 is not restored,
	 * which is not a problem as NS is not running yet and the reset value
	 * of zcr_el2 is unknown as per Arm ARM.
	 */
	write_zcr_el2(read_zcr_el2() | INPLACE(ZCR_EL2_LEN, SVE_VQ_ARCH_MAX));
	isb();
	sve_max_vq = SVE_VL_TO_VQ(sve_rdvl());

	/* Restore saved cptr */
	write_cptr_el2(cptr_saved);
	isb();

	/* Update global CPU SIMD config */
	g_simd_cfg.sve_en = true;
	g_simd_cfg.sve_vq = sve_max_vq;
}

/* Find the architecturally permitted (Streaming Vector Length) SVL */
static void sme_init_once(void)
{
	uint32_t __unused sme_svq_arch_max;
	unsigned long cptr_new, cptr_saved;
	uint64_t smcr_val;

	cptr_saved = read_cptr_el2();

	/* Enable access to FPU, SVE, SME */
	cptr_new = cptr_saved |
		INPLACE(CPTR_EL2_VHE_FPEN, CPTR_EL2_VHE_FPEN_NO_TRAP_11) |
		INPLACE(CPTR_EL2_VHE_ZEN, CPTR_EL2_VHE_ZEN_NO_TRAP_11) |
		INPLACE(CPTR_EL2_VHE_SMEN, CPTR_EL2_VHE_SMEN_NO_TRAP_11);
	write_cptr_el2(cptr_new);
	isb();

	/*
	 * Arm SME supplement recommends to request an out of range vector
	 * length of 8192 bytes by writing 0x1ff to SMCR_ELx[8:0]. Reading back
	 * the register will give the max architecturally permitted SVQ.
	 *
	 * The old smcr_el2 is not restored as this is called only once during
	 * cold boot.
	 */
	smcr_val = read_smcr_el2();
	smcr_val |= MASK(SMCR_EL2_RAZ_LEN);
	write_smcr_el2(smcr_val);
	isb();
	sme_svq_arch_max = (uint32_t)EXTRACT(SMCR_EL2_RAZ_LEN, read_smcr_el2());

	/*
	 * Streaming SVE shares SVE register set Z/P/FFR. RMM will save and
	 * restore Streaming SVE state in 'sve_state', and 'sve_state' can hold
	 * vector registers for up to 2048 bits (vq: 15). If Streaming SVE mode
	 * reports a larger value than SVE_VQ_ARCH_MAX, then assert. Hopefully
	 * we won't hit this condition in the near future.
	 */
	assert(sme_svq_arch_max <= SVE_VQ_ARCH_MAX);

	/* Restore saved cptr */
	write_cptr_el2(cptr_saved);
	isb();

	/* Update global CPU SIMD config */
	g_simd_cfg.sme_en = true;
}

/*
 * This function initializes the SIMD layer depending on SIMD capability of the
 * CPU (FEAT_SVE/FEAT_SME).
 */
void simd_init(void)
{
	/* Init once */
	if (g_simd_init_done) {
		return;
	}

	if (is_feat_sve_present()) {
		sve_init_once();
	}

	if (is_feat_sme_present()) {
		sme_init_once();
	}

	g_simd_init_done = true;
}

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

#define is_ctx_init_done(sc)	(((sc)->sflags & SIMD_SFLAG_INIT_DONE) != 0U)
#define is_ctx_saved(sc)	(((sc)->sflags & SIMD_SFLAG_SAVED) != 0U)

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

	/* Save SVE vector registers */
	if (simd_has_sve(ctx)) {
		/* Saving SVE Z registers emcompasses FPU Q registers */
		sve_save_vector_registers(&ctx->vregs.sve, true);
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
}

static void restore_simd_context(struct simd_context *ctx)
{
	/*
	 * Restore EL2 config registers of this context before restoring vector
	 * registers.
	 */
	restore_simd_el2_config(ctx, &ctx->el2_regs);

	/* Restore SVE vector registers */
	if (simd_has_sve(ctx)) {
		/* Restoring SVE Z registers emcompasses FPU Q registers */
		sve_restore_vector_registers(&ctx->vregs.sve, true);
	} else {
		/* Restore FPU Q registers */
		fpu_restore_registers(&ctx->vregs.fpu);
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

		/* Disable appropriate traps */
		if (read_cptr_el2() != ctx_save->cptr_el2) {
			write_cptr_el2(ctx_save->cptr_el2);
			isb();
		}

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

	/*
	 * Construct the cptr_el2 to be used when this context needs to be
	 * saved and used by the owner.
	 */
	simd_ctx->cptr_el2 = CPTR_EL2_VHE_INIT;
	simd_ctx->cptr_el2 |= INPLACE(CPTR_EL2_VHE_FPEN,
				      CPTR_EL2_VHE_FPEN_NO_TRAP_11);

	/* Initialize SVE related fields and config registers */
	if (simd_cfg->sve_en) {
		simd_ctx->tflags |= SIMD_TFLAG_SVE;

		simd_ctx->el2_regs.zcr_el2 = 0UL;
		simd_ctx->el2_regs.zcr_el2 |= INPLACE(ZCR_EL2_LEN,
						      simd_cfg->sve_vq);

		simd_ctx->cptr_el2 |= INPLACE(CPTR_EL2_VHE_ZEN,
					      CPTR_EL2_VHE_ZEN_NO_TRAP_11);
	}

	simd_ctx->sflags |= SIMD_SFLAG_INIT_DONE;

	return 0;
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

/*
 * This function initializes the SIMD layer depending on SIMD capability of the
 * CPU (FPU/SVE). If CPU supports SVE, the max VQ will be discovered. Global
 * 'g_simd_cfg' will hold the CPU SIMD configuration discovered during init.
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

	g_simd_init_done = true;
}

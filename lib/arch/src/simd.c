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

/*
 * Global to store the max vq length supported by the CPU. We expect all CPUs
 * in the system to support the same max vq length.
 */
static int32_t g_sve_max_vq = -1;

/*
 * The default CPU simd type is set as FPU. During init time, if CPU supports
 * SVE (which encompasses FPU), this will be updated to SIMD_SVE.
 */
static simd_t g_cpu_simd_type = SIMD_FPU;

/* This structure is used for storing FPU or SVE context for NS world. */
struct ns_simd_state {
	struct simd_state simd;
	uint64_t ns_zcr_el2;
	bool saved;
} __attribute__((aligned(CACHE_WRITEBACK_GRANULE)));

static struct ns_simd_state g_ns_simd[MAX_CPUS];

static bool g_simd_state_saved[MAX_CPUS];

/*
 * Returns 'true' if the current CPU's SIMD (FPU/SVE) live state is saved in
 * memory else 'false'.
 */
bool simd_is_state_saved(void)
{
	return g_simd_state_saved[my_cpuid()];
}

/*
 * Program the ZCR_EL2.LEN field from the VQ, if current ZCR_EL2.LEN is not same
 * as the passed in VQ.
 */
static void sve_config_vq(uint8_t vq)
{
	u_register_t zcr_val;

	zcr_val = read_zcr_el2();
	if (EXTRACT(ZCR_EL2_LEN, zcr_val) != vq) {
		zcr_val &= ~MASK(ZCR_EL2_LEN);
		zcr_val |= INPLACE(ZCR_EL2_LEN, vq);
		write_zcr_el2(zcr_val);
		isb();
	}
}

/*
 * Save FPU or SVE state from registers to memory. The caller must disable
 * traps for the corresponding 'type'. In case of SVE state, the vq from the
 * sve state is programmed to ZCR_EL2.LEN before saving the state. As this
 * function will modify ZCR_EL2, the caller needs to save the value of this
 * register if it needs to be preserved.
 */
void simd_save_state(simd_t type, struct simd_state *simd)
{
	assert(simd != NULL);
	assert(simd->simd_type == SIMD_NONE);

	switch (type) {
	case SIMD_FPU:
		assert(is_fpen_enabled());
		fpu_save_state((uint8_t *)&simd->t.fpu);
		break;
	case SIMD_SVE:
		assert(is_feat_sve_present() == true);
		assert(is_zen_enabled() && is_fpen_enabled());

		/*
		 * Configure zcr_el2 before saving the vector registers:
		 *  For NS state : max_vq restricted by EL3 (g_sve_max_vq)
		 *  For Realms   : max_vq of Realm
		 */
		sve_config_vq(simd->t.sve.vq);

		/* Save SVE vector registers Z0-Z31 */
		sve_save_z_state((uint8_t *)&simd->t.sve.z);
		/* Save SVE P0-P15, FFR registers */
		sve_save_p_ffr_state((uint8_t *)&simd->t.sve.p);
		/* Save SVE ZCR_EL12 and FPU status register */
		sve_save_zcr_fpu_state((uint8_t *)&simd->t.sve.zcr_el12);
		break;
	default:
		assert(false);
	}
	simd->simd_type = type;
	g_simd_state_saved[my_cpuid()] = true;
}

/*
 * Restore FPU or SVE state from memory to registers. The caller must disable
 * traps for the corresponding 'type'. In case of SVE state, the vq from the
 * sve state is programmed to ZCR_EL2.LEN before restoring the state.
 */
void simd_restore_state(simd_t type, struct simd_state *simd)
{
	assert(simd != NULL);
	switch (type) {
	case SIMD_FPU:
		assert(is_fpen_enabled());
		assert(simd->simd_type == SIMD_FPU);
		fpu_restore_state((uint8_t *)&simd->t.fpu);
		break;
	case SIMD_SVE:
		assert(is_feat_sve_present() == true);
		assert(is_zen_enabled() && is_fpen_enabled());
		assert(simd->simd_type == SIMD_SVE);

		/*
		 * Before restoring vector registers, set ZCR_EL2.LEN to the
		 * context's VQ that needs to be restored.
		 */
		sve_config_vq(simd->t.sve.vq);

		/* Restore SVE vector registers Z0-Z31 */
		sve_restore_z_state((uint8_t *)&simd->t.sve.z);
		/* Restore SVE FFR, P0-P15 registers */
		sve_restore_ffr_p_state((uint8_t *)&simd->t.sve.p);
		/* Restore SVE ZCR_EL12 and FPU status register */
		sve_restore_zcr_fpu_state((uint8_t *)&simd->t.sve.zcr_el12);
		break;
	default:
		assert(false);
	}
	simd->simd_type = SIMD_NONE;
	g_simd_state_saved[my_cpuid()] = false;
}

/*
 * Save NS SIMD state based on CPU SIMD type. For SVE, save the current zcr_el2
 * and call simd_save_state() which will save the SVE state (Z, P, FFR) after
 * setting the zcr_el2 to max VQ
 */
void simd_save_ns_state(void)
{
	unsigned int cpu_id = my_cpuid();
	simd_t stype;

	assert(g_ns_simd[cpu_id].saved == false);
	stype = g_cpu_simd_type;

	simd_enable(stype);
	/*
	 * Save the NS zcr_el2 value since EL3 doesn't bank this. Note that the
	 * save of NS SVE context occurs with MAX_SVE_VL to prevent leakage.
	 */
	if (stype == SIMD_SVE) {
		g_ns_simd[cpu_id].ns_zcr_el2 = read_zcr_el2();
	}
	simd_save_state(stype, &g_ns_simd[cpu_id].simd);
	simd_disable();
	g_ns_simd[cpu_id].saved = true;
}

/*
 * Restore NS SIMD state based on CPU SIMD type. For SVE, the
 * simd_restore_state() will set zcr_el2 to max VQ and restore the SVE state
 * (Z, P, FFR) registers.
 */
void simd_restore_ns_state(void)
{
	unsigned int cpu_id = my_cpuid();
	simd_t stype;

	assert(g_ns_simd[cpu_id].saved == true);
	stype = g_cpu_simd_type;

	simd_enable(stype);
	simd_restore_state(stype, &g_ns_simd[cpu_id].simd);
	/*
	 * Note that the restore SVE state for NS state happens with
	 * MAX_SVE_VL to prevent leakage. RMM now needs to restore the NS zcr_el2
	 * value since EL3 is not saving this.
	 */
	if (stype == SIMD_SVE) {
		write_zcr_el2(g_ns_simd[cpu_id].ns_zcr_el2);
		isb();
	}
	simd_disable();
	g_ns_simd[cpu_id].saved = false;
}

/* Return the SVE max vq discovered during init */
unsigned int simd_sve_get_max_vq(void)
{
	assert(is_feat_sve_present() == true);
	assert(g_sve_max_vq != -1);
	return (unsigned int)g_sve_max_vq;
}

/*
 * Initializes simd_state. Set the 'type' in simd state and if 'type' is
 * SVE then set the 'sve_vq' in simd state. This interface is called by REC
 */
void simd_state_init(simd_t type, struct simd_state *simd, uint8_t sve_vq)
{
	assert(simd != NULL);
	assert((type == SIMD_FPU) || (type == SIMD_SVE));
	assert(simd->simd_type == SIMD_NONE);

	/*
	 * TODO: bzero simd state. Currently the simd context is assumed to be
	 * zeroed out but with FEAT_MEC enabled, the simd context in AUX granule
	 * might not be zeroed out.
	 */
	if (type == SIMD_SVE) {
		assert(sve_vq <= (uint8_t)g_sve_max_vq);
		simd->t.sve.vq = sve_vq;
	}
	simd->simd_type = type;
}

/* Find the SVE max vector length restricted by EL3 */
static void sve_init(void)
{
	/* Check if g_sve_max_vq is initialized */
	if (g_sve_max_vq != -1) {
		return;
	}

	/*
	 * Write architecture max limit for vector length to ZCR_EL2.LEN and read
	 * back the sve vector length reported by rdvl. This will give the vector
	 * length limit set by EL3 for its lower ELs. RMM will use this value as
	 * max limit for EL2 and lower ELs.
	 */
	simd_enable(SIMD_SVE);

	/*
	 * Configure ZCR.LEN to SVE_VQ_ARCH_MAX, the old zcr_el2 is not restored
	 * as this is called only once during cold boot.
	 */
	sve_config_vq(SVE_VQ_ARCH_MAX);
	g_sve_max_vq = (int32_t)SVE_VL_TO_VQ(sve_rdvl());
	g_cpu_simd_type = SIMD_SVE;

	simd_disable();
}

/*
 * This function initializes the SIMD layer depending on SIMD capability of the
 * CPU (FPU/SVE). If CPU supports SVE, the max VQ will be discovered and NS SIMD
 * SVE state will be initialized with the max vq
 */
void simd_init(void)
{
	unsigned int cpu_id = my_cpuid();

	if (is_feat_sve_present()) {
		sve_init();
		/* Set the max vq in NS simd state */
		g_ns_simd[cpu_id].simd.t.sve.vq = (uint8_t)g_sve_max_vq;
	}
}

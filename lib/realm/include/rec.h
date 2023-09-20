/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef REC_H
#define REC_H

#ifndef __ASSEMBLER__

#include <arch.h>
#include <attestation_token.h>
#include <gic.h>
#include <memory_alloc.h>
#include <pauth.h>
#include <pmu.h>
#include <ripas.h>
#include <simd.h>
#include <sizes.h>
#include <smc-rmi.h>
#include <utils_def.h>

struct granule;

/*
 * System registers whose contents are specific to a REC.
 */
struct sysreg_state {
	unsigned long sp_el0;
	unsigned long sp_el1;
	unsigned long elr_el1;
	unsigned long spsr_el1;
	unsigned long pmcr_el0;
	unsigned long tpidrro_el0;
	unsigned long tpidr_el0;
	unsigned long csselr_el1;
	unsigned long sctlr_el1;
	unsigned long actlr_el1;
	unsigned long cpacr_el1;
	unsigned long zcr_el1;
	unsigned long ttbr0_el1;
	unsigned long ttbr1_el1;
	unsigned long tcr_el1;
	unsigned long esr_el1;
	unsigned long afsr0_el1;
	unsigned long afsr1_el1;
	unsigned long far_el1;
	unsigned long mair_el1;
	unsigned long vbar_el1;
	unsigned long contextidr_el1;
	unsigned long tpidr_el1;
	unsigned long amair_el1;
	unsigned long cntkctl_el1;
	unsigned long par_el1;
	unsigned long mdscr_el1;
	unsigned long mdccint_el1;
	unsigned long disr_el1;
	unsigned long mpam0_el1;

	/* Timer Registers */
	unsigned long cnthctl_el2;
	unsigned long cntvoff_el2;
	unsigned long cntpoff_el2;
	unsigned long cntp_ctl_el0;
	unsigned long cntp_cval_el0;
	unsigned long cntv_ctl_el0;
	unsigned long cntv_cval_el0;

	/* GIC Registers */
	struct gic_cpu_state gicstate;

	/* TODO MPAM */
	/* TODO Performance Monitor Registers */
	/* TODO Pointer Authentication Registers */

	unsigned long vmpidr_el2;	/* restored only */
	unsigned long hcr_el2;		/* restored only */
};

/*
 * System registers whose contents are
 * common across all RECs in a Realm.
 */
struct common_sysreg_state {
	unsigned long vttbr_el2;
	unsigned long vtcr_el2;
	unsigned long hcr_el2;
	unsigned long mdcr_el2;
};

/* This structure is used for storing FPU or SVE context for realm. */
struct rec_simd_state {
	struct simd_state *simd; /* Pointer to SIMD context in AUX page */
	bool simd_allowed; /* Set when REC is allowed to use SIMD */
};

/*
 * This structure is aligned on cache line size to avoid cache line trashing
 * when allocated as an array for N CPUs.
 */
struct ns_state {
	struct sysreg_state sysregs;
	unsigned long sp_el0;
	unsigned long icc_sre_el2;
	struct pmu_state *pmu;
} __attribute__((aligned(CACHE_WRITEBACK_GRANULE)));

/*
 * Data used when handling attestation requests
 */
struct rec_attest_data {
	unsigned char rmm_realm_token_buf[SZ_1K];
	size_t rmm_realm_token_len;

	struct token_sign_cntxt token_sign_ctx;

	/* Buffer allocation info used for heap init and management */
	struct buffer_alloc_ctx alloc_ctx;
};
COMPILER_ASSERT(sizeof(struct rec_attest_data) <= GRANULE_SIZE);

/*
 * This structure contains pointers to data that are allocated
 * in auxilary granules for a REC.
 */
struct rec_aux_data {
	/* Pointer to the heap buffer */
	uint8_t *attest_heap_buf;

	/* Pointer to PMU state */
	struct pmu_state *pmu;

	/* SIMD context region */
	struct rec_simd_state rec_simd;

	/* Pointer to attestation-related data */
	struct rec_attest_data *attest_data;
};

struct rec {
	struct granule *g_rec;	/* the granule in which this REC lives */
	unsigned long rec_idx;	/* which REC is this */
	bool runnable;

	unsigned long regs[31];

	/*
	 * PAuth state of Realm.
	 * Note that we do not need to save NS state as EL3 will save this as part of world switch.
	 */
	struct pauth_state pauth;

	unsigned long pc;
	unsigned long pstate;

	struct sysreg_state sysregs;
	struct common_sysreg_state common_sysregs;

	/* Populated when the REC issues a RIPAS change request */
	struct {
		unsigned long base;
		unsigned long top;
		unsigned long addr;
		enum ripas ripas_val;
		enum ripas_change_destroyed change_destroyed;
	} set_ripas;

	/*
	 * Common values across all RECs in a Realm.
	 */
	struct {
		unsigned long ipa_bits;
		int s2_starting_level;
		struct granule *g_rtt;
		struct granule *g_rd;
		bool pmu_enabled;
		unsigned int pmu_num_ctrs;
		enum hash_algo algorithm;
		bool sve_enabled;
		uint8_t sve_vq;
	} realm_info;

	struct {
		/*
		 * The contents of the *_EL2 system registers at the last time
		 * the REC exited to the host due to a synchronous exception.
		 * These are the unsanitized register values which may differ
		 * from the value returned to the host in rec_exit structure.
		 */
		unsigned long esr;
		unsigned long hpfar;
		unsigned long far;
	} last_run_info;

	/* Pointer to per-cpu non-secure state */
	struct ns_state *ns;

	struct {
		/*
		 * Set to 'true' when there is a pending PSCI
		 * command that must be resolved by the host.
		 * The command is encoded in rec->regs[0].
		 *
		 * A REC with pending PSCI is not schedulable.
		 */
		bool pending;
	} psci_info;

	/* Number of auxiliary granules */
	unsigned int num_rec_aux;

	/* Addresses of auxiliary granules */
	struct granule *g_aux[MAX_REC_AUX_GRANULES];
	struct rec_aux_data aux_data;
	struct {
		unsigned long vsesr_el2;
		bool inject;
	} serror_info;

	/* True if host call is pending */
	bool host_call;
};
COMPILER_ASSERT(sizeof(struct rec) <= GRANULE_SIZE);

/*
 * Check that mpidr has a valid value with all fields except
 * Aff3[39:32]:Aff2[23:16]:Aff1[15:8]:Aff0[3:0] set to 0.
 */
static inline bool mpidr_is_valid(unsigned long mpidr)
{
	return (mpidr & ~(MASK(MPIDR_EL2_AFF0) |
			  MASK(MPIDR_EL2_AFF1) |
			  MASK(MPIDR_EL2_AFF2) |
			  MASK(MPIDR_EL2_AFF3))) == 0ULL;
}

/*
 * Calculate REC index from mpidr value.
 * index = Aff3[39:32]:Aff2[23:16]:Aff1[15:8]:Aff0[3:0]
 */
static inline unsigned long mpidr_to_rec_idx(unsigned long mpidr)
{
	return (MPIDR_EL2_AFF(0, mpidr) +
		MPIDR_EL2_AFF(1, mpidr) +
		MPIDR_EL2_AFF(2, mpidr) +
		MPIDR_EL2_AFF(3, mpidr));
}

static inline simd_t rec_simd_type(struct rec *rec)
{
	if (rec->realm_info.sve_enabled) {
		return SIMD_SVE;
	}
	return SIMD_FPU;
}

static inline bool rec_is_simd_allowed(struct rec *rec)
{
	assert(rec != NULL);
	return rec->aux_data.rec_simd.simd_allowed;
}

void rec_run_loop(struct rec *rec, struct rmi_rec_exit *rec_exit);
void inject_serror(struct rec *rec, unsigned long vsesr);
void emulate_stage2_data_abort(struct rec *rec, struct rmi_rec_exit *rec_exit,
			       unsigned long rtt_level);

#endif /* __ASSEMBLER__ */
#endif /* REC_H */

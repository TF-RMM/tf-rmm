/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef REC_H
#define REC_H

#ifndef __ASSEMBLER__

#include <arch.h>
#include <attest_app.h>
#include <gic.h>
#include <pauth.h>
#include <planes.h>
#include <pmu.h>
#include <ripas.h>
#include <s2tt.h>
#include <simd.h>
#include <sizes.h>
#include <smc-rmi.h>
#include <timers.h>
#include <utils_def.h>

#ifndef CBMC
#define RMM_REC_SAVED_GEN_REG_COUNT	U(31)
#define REG_TYPE			unsigned long

/* Number of pages per REC for PMU state */
#define REC_PMU_PAGES			1U
#define REC_PMU_SIZE			(REC_PMU_PAGES * SZ_4K)

/* Ensure that we have enough space to store the PMU contexts per plane. */
COMPILER_ASSERT((sizeof(struct pmu_state) * MAX_TOTAL_PLANES) <= REC_PMU_SIZE);

/*
 * SIMD context that holds FPU/SVE registers. Space to save max arch supported
 * SVE vector length of 2048 bits.
 * Size of 32 Z registers (256 bytes each): 8192 bytes
 * Size of 16 P registers (32 bytes each) :  512 bytes
 * Size of 1 FFR register (32 bytes each) :   32 bytes
 * Size of other status registers         :   32 bytes
 * Total size is ~3 Pages (rounded up to page size).
 */
#define REC_SIMD_PAGES			3U
#define REC_SIMD_SIZE			(REC_SIMD_PAGES * SZ_4K)

/* Number of pages per REC for 'rec_attest_data' structure */
#define REC_ATTEST_PAGES		1U
#define REC_ATTEST_SIZE			(REC_ATTEST_PAGES * SZ_4K)

/* Number of pages per REC for storing sysregs for planes */
#define REC_SYSREGS_PAGES		1U
#define REC_SYSREGS_SIZE		(REC_SYSREGS_PAGES * SZ_4K)

/* Number of pages per REC to be allocated */
#define REC_NUM_PAGES		(REC_PMU_PAGES	  + \
				 REC_SIMD_PAGES	  + \
				 REC_ATTEST_PAGES + \
				 REC_SYSREGS_PAGES + \
				 RMM_CCA_TOKEN_BUFFER)

#else /* CBMC */
/*
 * struct rec must fit in a single granule. CBMC has a smaller GRANULE_SIZE
 * defined than on a real target, and the full structure doesn't fit there. The
 * following definitions help making the structure smaller.
 */
/*
 * For CBMC it is not necessary to have a regs array that fits all the 31
 * general registers
 */
#define RMM_REC_SAVED_GEN_REG_COUNT	SMC_RESULT_REGS
/* Reserve a single byte per saved register instead of 8. */
#define REG_TYPE			unsigned char

#define REC_PMU_PAGES		0U
#define REC_PMU_SIZE		(REC_PMU_PAGES * SZ_4K)

#define REC_SIMD_PAGES		0U
#define REC_SIMD_SIZE		(REC_SIMD_PAGES * SZ_4K)

#define REC_ATTEST_PAGES	0U
#define REC_ATTEST_SIZE		(REC_ATTEST_PAGES * SZ_4K)

#define REC_SYSREGS_PAGES	0U
#define REC_SYSREGS_SIZE	(REC_SYSREGS_PAGES * SZ_4K)

/* Number of aux granules pages per REC to be used */
#define REC_NUM_PAGES		(1U)
#endif /* CBMC */

struct granule;

/*
 * System registers whose contents are specific to a Plane.
 */
STRUCT_TYPE sysreg_state {
	/*
	 * Set of per plane system registers that can be accessed by Plane 0
	 * through RSI calls.
	 */
	STRUCT_TYPE plane_el01_regs pp_sysregs;

	/* Timer Registers */
	unsigned long cnthctl_el2;
	unsigned long cntvoff_el2;
	unsigned long cntpoff_el2;

	unsigned long pstate;
	unsigned long vttbr_el2;

	/* GIC Registers */
	/*
	 * TODO: It might be possible to break the gic_cpu_state structure
	 * into two different halves, one containing the per-realm GIC
	 * configuration and other once containing the per-plane GIC one.
	 * This way, we would only need to care about saving/restoring the
	 * affected half only.
	 */
	struct gic_cpu_state gicstate;

	/*
	 * Pointer to the PMU registers.
	 * Note that this is a pointer as pmu_state structure may have a
	 * large storage itself.
	 */
	struct pmu_state *pmu;

	unsigned long vmpidr_el2;	/* restored only */
	unsigned long hcr_el2;		/* restored only */

	unsigned long cptr_el2;		/* restored only */

#ifndef CBMC
	/*
	 * PAuth state of Plane.
	 * Note that we do not need to save NS state as EL3 will save this as part of world switch.
	 */
	struct pauth_state pauth;
#endif /* CBMC*/
};

COMPILER_ASSERT_NO_CBMC(REC_SYSREGS_SIZE >=
		(sizeof(STRUCT_TYPE sysreg_state) * MAX_TOTAL_PLANES));

/*
 * System registers whose contents are
 * common across all RECs in a Realm.
 */
STRUCT_TYPE common_sysreg_state {
	unsigned long vtcr_el2;
	unsigned long hcr_el2;
	unsigned long mdcr_el2;
};

/*
 * This structure is aligned on cache line size to avoid cache line trashing
 * when allocated as an array for N CPUs.
 */
struct ns_state {
	STRUCT_TYPE sysreg_state sysregs;
	unsigned long icc_sre_el2;
	unsigned long s2por_el1;
	struct pmu_state pmu;
	struct timer_state el2_timer;
} __aligned(CACHE_WRITEBACK_GRANULE);

/*
 * Data used when handling attestation requests
 */
struct rec_attest_data {
	size_t rmm_realm_token_len;

	/* Number of CCA token bytes copied to the Realm */
	size_t rmm_cca_token_copied_len;

	/* Number of CCA token bytes left to copy to the Realm */
	size_t rmm_cca_token_len;
};
COMPILER_ASSERT(sizeof(struct rec_attest_data) <= GRANULE_SIZE);

/*
 * This structure contains pointers to data that are allocated
 * in auxilary granules for a REC.
 */
struct rec_aux_data {
	/* SIMD context region */
	struct simd_context *simd_ctx;

	/* Pointer to attestation-related data */
	struct rec_attest_data *attest_data;

	/* Address of the per-plane sysreg data */
	STRUCT_TYPE sysreg_state *sysregs;
};

/*
 * Per-plane specific REC data.
 */
struct rec_plane {
	REG_TYPE regs[RMM_REC_SAVED_GEN_REG_COUNT];

	STRUCT_TYPE sysreg_state *sysregs;
	unsigned long pc;

	bool trap_hc;
	bool trap_simd;

	STRUCT_TYPE {
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
};

/*
 * The RmmRecResponse enumeration represents whether the Host accepted
 * or rejected a Realm request.
 *
 * Map RmmRecResponse to RmiResponse to simplify check operation.
 */
enum host_response {
	ACCEPT = RMI_ACCEPT,	/* Host accepted Realm request */
	REJECT = RMI_REJECT	/* Host rejected Realm request */
};

struct rec { /* NOLINT: Suppressing optin.performance.Padding as fields are in logical order */
	struct granule *g_rec;	/* the granule in which this REC lives */
	unsigned long rec_idx;	/* which REC is this */
	bool runnable;

	/*
	 * We keep a local copy of Plane_0 and another one
	 * for the current Plane_N
	 */
	struct rec_plane plane[2];

	STRUCT_TYPE common_sysreg_state common_sysregs;

	/* Populated when the REC issues a RIPAS change request */
	struct {
		unsigned long base;
		unsigned long top;
		unsigned long addr;
		enum ripas ripas_val;
		enum ripas_change_destroyed change_destroyed;
		enum host_response response;
	} set_ripas;

	/*
	 * Populated when the REC issues a request to change
	 * Overlay Permission Index.
	 */
	struct {
		unsigned long top;
		unsigned long base;
		unsigned long index;
		unsigned long cookie;
		enum host_response response;
	} set_s2ap;

	/*
	 * Common values across all RECs in a Realm.
	 */
	struct {
		struct granule *g_rd;
		bool pmu_enabled;
		unsigned int pmu_num_ctrs;
		enum hash_algo algorithm;
		struct simd_config simd_cfg;
		struct s2tt_context primary_s2_ctx;
		unsigned int num_aux_planes;
		bool rtt_tree_pp;
		bool rtt_s2ap_encoding;
	} realm_info;

	/* Pointer to per-cpu non-secure state */
	struct ns_state *ns;

	struct {
		/*
		 * Set to 'true' when there is a pending PSCI
		 * command that must be resolved by the host.
		 * PSCI is an SMC call, which means it will be trapped
		 * to plane0 and then plane0 will issue it so the
		 * command is encoded in regs[0] of plane0.
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

	struct app_data_cfg attest_app_data;

	/* The active SIMD context that is live in CPU registers */
	struct simd_context *active_simd_ctx;

	/* Index of the currently active plane */
	unsigned int active_plane_id;

	/* GIC Owner plane id */
	unsigned int gic_owner;
};
COMPILER_ASSERT(sizeof(struct rec) <= GRANULE_SIZE);

/*
 * Retrieve a pointer to the sysregs given a rec structure and a plane index.
 * Note that this macro does not do any sanitization to the arguments.
 */
#define REC_GET_SYSREGS_FROM_AUX(_rec, _index)				\
	({								\
		STRUCT_TYPE sysreg_state *_sysreg =			\
			&((_rec)->aux_data.sysregs[(_index)]);		\
									\
		_sysreg;						\
	})

/*
 * Get the number of planes available on the realm
 */
static inline unsigned int rec_num_planes(struct rec *rec)
{
	return rec->realm_info.num_aux_planes + 1U;
}

/* Activate and return an auxiliary plane */
static inline struct rec_plane *rec_activate_plane_n(struct rec *rec,
						     unsigned int plane_idx)
{
	assert(plane_idx > PLANE_0_ID);
	assert(plane_idx < rec_num_planes(rec));
	assert(rec->active_plane_id == PLANE_0_ID);

	rec->active_plane_id = plane_idx;

	rec->plane[1].sysregs = &rec->aux_data.sysregs[plane_idx];
	return &rec->plane[1];
}

/* Deactivate an auxiliary plane */
static inline void rec_deactivate_plane_n(struct rec *rec)
{
	assert(rec->active_plane_id != PLANE_0_ID);

	rec->active_plane_id = PLANE_0_ID;
	rec->plane[1].sysregs = NULL;
}

/*
 * Return 'true' if the active plane is Plane 0.
 */
static inline bool rec_is_plane_0_active(struct rec *rec)
{
	return (rec->active_plane_id == PLANE_0_ID);
}

/*
 * Return the S2 context ID of the currently active plane given a REC
 */
static inline unsigned int active_s2_context_idx(struct rec *rec)
{
	unsigned int plane_id = rec->active_plane_id;

	assert(plane_id < rec_num_planes(rec));

	return ((plane_id + 1U) % rec_num_planes(rec));
}

/*
 * Get the part of the REC which corresponds to Plane 0.
 */
static inline struct rec_plane *rec_plane_0(struct rec *rec)
{
	return &rec->plane[PLANE_0_ID];
}

/* Get the part of the REC which corresponds to the currently active plane. */
static inline struct rec_plane *rec_active_plane(struct rec *rec)
{
	struct rec_plane *plane =  (rec->active_plane_id == PLANE_0_ID) ?
						rec_plane_0(rec) : &rec->plane[1];

	assert(plane->sysregs != NULL);

	return plane;
}

/*
 * Check that mpidr of RmiRecMpidr type has a valid value with all fields except
 * Aff3[31:24]:Aff2[23:16]:Aff1[15:8]:Aff0[3:0] set to 0.
 */
static inline bool rec_mpidr_is_valid(unsigned long rec_mpidr)
{
	return (rec_mpidr & ~(MASK(RMI_MPIDR_AFF0) |
			  MASK(RMI_MPIDR_AFF1) |
			  MASK(RMI_MPIDR_AFF2) |
			  MASK(RMI_MPIDR_AFF3))) == 0ULL;
}

/*
 * Calculate REC index from mpidr of RmiRecMpidr type value.
 * index = Aff3[31:24]:Aff2[23:16]:Aff1[15:8]:Aff0[3:0]
 */
static inline unsigned long rec_mpidr_to_idx(unsigned long rec_mpidr)
{
	return (RMI_MPIDR_AFF(0, rec_mpidr) |
		RMI_MPIDR_AFF(1, rec_mpidr) |
		RMI_MPIDR_AFF(2, rec_mpidr) |
		RMI_MPIDR_AFF(3, rec_mpidr));
}

/*
 * Calculate REC index from mpidr of MPIDR_EL1 register type
 * Aff3[39:32]:Aff2[23:16]:Aff1[15:8]:Aff0[3:0]
 */
static inline unsigned long mpidr_to_rec_idx(unsigned long mpidr)
{
	return (MPIDR_EL1_AFF(0, mpidr) |
		MPIDR_EL1_AFF(1, mpidr) |
		MPIDR_EL1_AFF(2, mpidr) |
		MPIDR_EL1_AFF(3, mpidr));
}

/*
 * Convert mpidr of RmiRecMpidr type
 * Aff3[31:24]:Aff2[23:16]:Aff1[15:8]:Aff0[3:0]
 * to MPIDR_EL1 register type value
 * Aff3[39:32]:Aff2[23:16]:Aff1[15:8]:Aff0[3:0].
 */
static inline unsigned long rec_mpidr_to_mpidr(unsigned long rec_mpidr)
{
	return (rec_mpidr & (MASK(RMI_MPIDR_AFF0)	|
			 MASK(RMI_MPIDR_AFF1)	|
			 MASK(RMI_MPIDR_AFF2)))	|
		((rec_mpidr & MASK(RMI_MPIDR_AFF3)) <<
			(MPIDR_EL1_AFF3_SHIFT - RMI_MPIDR_AFF3_SHIFT));
}

/*
 * Runs the Realm REC provided at @rec until a REC exit happens that needs
 * to be handled by the Host.
 *
 * @rec_exit contains the data passed to the Host on REC exit.
 *
 * Note that this API assumes that the REC and the REC_AUX granules
 * are mapped upon calling it.
 */
void rec_run_loop(struct rec *rec, struct rmi_rec_exit *rec_exit);
void inject_serror(struct rec *rec, unsigned long vsesr);
void emulate_stage2_data_abort(struct rmi_rec_exit *rec_exit,
			       unsigned long rtt_level, unsigned long ipa);

#endif /* __ASSEMBLER__ */
#endif /* REC_H */

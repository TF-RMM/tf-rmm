/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIMD_H
#define SIMD_H

#include <arch.h>
#include <arch_features.h>
#include <assert.h>
#include <fpu_helpers.h>
#include <stddef.h>
#include <sve_helpers.h>

typedef enum {
	SIMD_NONE,
	SIMD_FPU,
	SIMD_SVE
} simd_t;

struct simd_state {
	union {
		struct fpu_state fpu;
		struct sve_state sve;
	} t;
	simd_t simd_type;
};

/* Initialize simd layer based on CPU support for FPU or SVE */
void simd_init(void);

/* Return the max SVE vq discovered by RMM */
unsigned int simd_sve_get_max_vq(void);

/* Save SIMD state to memory pointed by 'simd' based on simd 'type'. */
void simd_save_state(simd_t type, struct simd_state *simd);

/* Restore SIMD state from memory pointed by 'simd' based on simd 'type'. */
void simd_restore_state(simd_t type, struct simd_state *simd);

/*
 * Initialize the simd_state before using this first time for a REC. The 'sve_vq'
 * parameter will be used to initialize SVE VQ length in case the simd type is
 * SVE or else it is ignored.
 */
void simd_state_init(simd_t type, struct simd_state *simd, uint8_t sve_vq);

/*
 * Save NS FPU or SVE state from registers to memory. This function dynamically
 * determines the SIMD type based on CPU SIMD capability.
 * TODO: Cater for SVE hint bit.
 */
void simd_save_ns_state(void);

/*
 * Restore NS FPU or SVE state from memory to registers. This function
 * dynamically determines the SIMD type based on CPU SIMD capability.
 * TODO: Cater for SVE hint bit.
 */
void simd_restore_ns_state(void);

/* Allow FPU and/or SVE access */
static inline void simd_enable(simd_t type)
{
	unsigned long cptr;

	cptr = read_cptr_el2();
	cptr &= ~(MASK(CPTR_EL2_FPEN) | MASK(CPTR_EL2_ZEN));

	switch (type) {
	case SIMD_SVE:
		assert(is_feat_sve_present());

		cptr |= INPLACE(CPTR_EL2_ZEN, CPTR_EL2_ZEN_NO_TRAP_11);
		cptr |= INPLACE(CPTR_EL2_FPEN, CPTR_EL2_FPEN_NO_TRAP_11);
		break;
	case SIMD_FPU:
		cptr |= INPLACE(CPTR_EL2_ZEN, CPTR_EL2_ZEN_TRAP_ALL_00);
		cptr |= INPLACE(CPTR_EL2_FPEN, CPTR_EL2_FPEN_NO_TRAP_11);
		break;
	default:
		assert(false);
	}

	write_cptr_el2(cptr);
	isb();
}

/* Deny FPU and SVE access */
static inline void simd_disable(void)
{
	unsigned long cptr;

	cptr = read_cptr_el2();
	cptr &= ~(MASK(CPTR_EL2_FPEN) | MASK(CPTR_EL2_ZEN));

	cptr |= INPLACE(CPTR_EL2_ZEN, CPTR_EL2_ZEN_TRAP_ALL_00);
	cptr |= INPLACE(CPTR_EL2_FPEN, CPTR_EL2_FPEN_TRAP_ALL_00);

	write_cptr_el2(cptr);
	isb();
}

/*
 * These functions and macros will be renamed to simd_* once RMM supports
 * SIMD (FPU/SVE) at REL2
 */
#ifdef RMM_FPU_USE_AT_REL2
#define FPU_ALLOW(expression) \
	do { \
		assert(false); \
		expression; \
	} while (false)

#define IS_FPU_ALLOWED() \
	(false)

#else /* RMM_FPU_USE_AT_REL2 */
#define FPU_ALLOW(expression) \
	do { \
		expression; \
	} while (false)

#define IS_FPU_ALLOWED() (true)

#endif /* RMM_FPU_USE_AT_REL2 */

/*
 * Save/restore FPU state to/from a per-cpu buffer allocated within the library.
 * The FPU instruction trap is disabled by this function during the access to
 * the FPU registers.
 * These functions are expected to be called before FPU is used by RMM to save
 * the incoming FPU context.
 */
void fpu_save_my_state(void);
void fpu_restore_my_state(void);

/*
 * Return true if an SIMD state is saved in the per-cpu buffer in this library.
 *
 * After calling 'fpu_save_my_state' this function returns true. After calling
 * 'fpu_restore_my_state' this function returns false.
 */
bool fpu_is_my_state_saved(unsigned int cpu_id);

#endif /* SIMD_H */

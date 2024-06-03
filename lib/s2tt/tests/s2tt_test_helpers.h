/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef S2TT_TEST_HELPERS_H
#define S2TT_TEST_HELPERS_H

#include <arch_helpers.h>
#include <granule_types.h>
#include <utils_def.h>

/* Macros to specify LPA2 status */
#define LPA2_ENABLED					(true)
#define LPA2_DISABLED					(false)

/*
 * Helper macro definitions.
 * When possible, we try not to rely on the SUT own definitions, to
 * avoid poisoning if any of them are buggy.
 *
 * Some essential definions which rely on build options are taken from
 * the SUT definitions, though (e.g. {MIN, MAX}_IPA_BITS and such).
 */
#define S2TT_TEST_HELPERS_MIN_LVL	(0L)
#define S2TT_TEST_HELPERS_MIN_LVL_LPA2	(-1L)
#define S2TT_TEST_HELPERS_MAX_LVL	(3L)
#define S2TT_TEST_HELPERS_MAX_TABLE_LVL (2L)

/* TTE type */
#define S2TT_TEST_DESC_TYPE_WIDTH	(2UL)
#define S2TT_TEST_DESC_TYPE_SHIFT	(0UL)
#define S2TT_TEST_DESC_TYPE_MASK	MASK(S2TT_TEST_DESC_TYPE)
#define S2TT_TEST_INVALID_DESC		INPLACE(S2TT_TEST_DESC_TYPE, 0x0UL)
#define S2TT_TEST_BLOCK_DESC		INPLACE(S2TT_TEST_DESC_TYPE, 0x1UL)
#define S2TT_TEST_PAGE_DESC		INPLACE(S2TT_TEST_DESC_TYPE, 0x3UL)
#define S2TT_TEST_TABLE_DESC		INPLACE(S2TT_TEST_DESC_TYPE, 0x3UL)

/*
 * When FEAT_LPA2 is enabled, the 2 MSB bits of the OA is not contiguous
 * to the rest of the address in the TTE.
 */
#define S2TT_TEST_OA_MSB_SHIFT		50U
#define S2TT_TEST_OA_MSB_WIDTH		2U

/* Where the 2 MSB bits of the OA are stored in the TTE */
#define S2TT_TEST_MSB_SHIFT		8U
#define S2TT_TEST_MSB_WIDTH		S2TT_TEST_OA_MSB_WIDTH
#define S2TT_TEST_MSB_MASK		MASK(S2TT_TEST_MSB)

/* Invalid value for the RIPAS field */
#define S2TT_TEST_RIPAS_INVALID		(3UL)

/*
 * Function to setup the environment for the tests specifying
 * whether FEAT_LPA2 is supported or not.
 */
void s2tt_test_helpers_setup(bool lpa2);

/* Get the PA mapped into a specific S2TTE */
unsigned long s2tt_test_helpers_s2tte_to_pa(unsigned long s2tte, long level);

/* Map a PA into a specific S2TTE */
unsigned long s2tt_test_helpers_pa_to_s2tte(unsigned long pa, long level);

/* Get the PA mask for a given level */
unsigned long s2tt_test_helpers_lvl_mask(long level);

/* Get the S2TTE PA mask */
unsigned long s2tt_test_helpers_s2tte_oa_mask(void);

/*
 * Generates an IPA aligned @level
 * Params:
 *	- level: Level for which the address will be generated. This will
 *		 define the minimum value for the address.
 *	- aligned: If 'true' the address will be aligned to 'level'. If 'false'
 *		   the address might or might not be aligned.
 */
unsigned long s2tt_test_helpers_gen_addr(long level, bool aligned);

/* Retrieve the attributes for a given tte */
unsigned long s2tt_test_helpers_s2tte_to_attrs(unsigned long tte, bool ns);

/*
 * Generate random attributes for a NS-TTE
 * Params:
 *	- host: If 'true', it generates a random set of attributes
 *		controlled by the host. If 'false;, it generates
 *		a random set of attibutes controlled by RMM.
 *	- reserved: If host == 'true', this flag determines whether
 *		    the HS or the MEMATTR fields on the host attributes
 *		    will be set to RESERVED or not. If 'true' either one
 *		    or both of the fields can be set to RESERVED, which
 *		    will make the descriptor invalid.
 */
unsigned long s2tt_test_helpers_gen_ns_attrs(bool host, bool reserved);

/*
 * Generate attributes for a secure TTE
 * Params:
 *	- invalid: If 'true', it will generate a valid TTE (e.g. the
 *		   descriptor type will be other than INVALID). When
 *		   'false, it will generate a valid TTE.
 *	- level: Level of the TTE when 'invalid' == 'false'.
 */
unsigned long s2tt_test_helpers_gen_attrs(bool invalid, long level);

/* Get the minimum table level */
long s2tt_test_helpers_min_table_lvl(void);

/* Get the minimum block level */
long s2tt_test_helpers_min_block_lvl(void);

/* For a given level return the VA space size of an S2TTE entry at such level */
unsigned long s2tt_test_helpers_get_entry_va_space_size(long level);

/* For a given address and level, return the index @level table for 'addr' */
unsigned long s2tt_test_helpers_get_idx_from_addr(unsigned long addr,
						  long level);

/* Helper to know whether LPA2 is enabled or not for the current test */
bool s2tt_test_helpers_lpa2_enabled(void);

/* Helper to create an assigned S2TTE as per the passed parameters */
unsigned long s2tt_test_create_assigned(const struct s2tt_context *s2tt_ctx,
					unsigned long pa, long level,
					unsigned long ripas);

/* Helper to create an unassigned S2TTE as per the passed parameters */
unsigned long s2tt_test_create_unassigned(const struct s2tt_context *s2tt_ctx,
					  unsigned long ripas);

/* Helper to modify the state of a granule without making any pre-checks */
static inline void s2tt_test_granule_set_state(struct granule *g,
					       unsigned int state)
{
	g->descriptor = (g->descriptor & ~STATE_MASK) | INPLACE(GRN_STATE, state);
}

/*
 * Helper to modify the locked state of a granule without making any pre-checks
 */
static inline void s2tt_test_granule_set_lock(struct granule *g,
					      bool locked)
{
	g->descriptor = (locked) ?
		(g->descriptor | GRN_LOCK_BIT) : (g->descriptor & ~GRN_LOCK_BIT);
}

#endif /* XLAT_TEST_HELPERS_H */

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

/* This file is derived from xlat_table_v2 library in TF-A project */

#ifndef XLAT_TABLES_PRIVATE_H
#define XLAT_TABLES_PRIVATE_H

#include <stdbool.h>
#include <xlat_contexts.h>

/* Determine the physical address space encoded in the 'attr' parameter. */
uint64_t xlat_arch_get_pas(uint64_t attr);

/*
 * Invalidate all TLB entries that match the given virtual address. This
 * operation applies to all PEs in the same Inner Shareable domain as the PE
 * that executes this function. This functions must be called for every
 * translation table entry that is modified. It only affects the EL2
 * Translate regime
 */
void xlat_arch_tlbi_va(uintptr_t va);

/*
 * This function has to be called at the end of any code that uses the function
 * xlat_arch_tlbi_va().
 */
void xlat_arch_tlbi_va_sync(void);

/* Print VA, PA, size and attributes of all regions in the mmap array. */
void xlat_mmap_print(const struct xlat_ctx *ctx);

/*
 * Print the current state of the translation tables by reading them from
 * memory.
 */
void xlat_tables_print(struct xlat_ctx *ctx);

/*
 * Returns a block/page table descriptor for the given level and attributes.
 */
uintptr_t xlat_desc(uint64_t attr, uintptr_t addr_pa, unsigned int level);

/*
 * Return the maximum physical address supported by the hardware.
 */
uintptr_t xlat_arch_get_max_supported_pa(void);

/*
 * Return the unpriviledged execute-never mask that will prevent instruction
 * fetch by EL0 at the EL2&0 translation regime.
 */
#define XLAT_GET_UXN_DESC() (UPPER_ATTRS(UXN))

/*
 * Return the priviledged execute-never mask that will prevent instruction
 * fetch by EL2 at the EL2&0 translation regime.
 */
#define XLAT_GET_PXN_DESC() (UPPER_ATTRS(PXN))

/*
 * Return the contiguous mask for a page or block descriptor
 */
#define XLAT_GET_CONT_HINT() (UPPER_ATTRS(CONT_HINT))

/*
 * Return the NG flag for a page or block descriptor
 */
#define XLAT_GET_NG_HINT() (LOWER_ATTRS(NG_HINT))

/*
 * Set up the xlat_ctx_cfg field of a given context.
 * This macro doesn't check parameters.
 *
 * _ctx:
 *   Pointer to xlat_ctx.
 *
 * _cfg:
 *   reference to xlat_ctx_cfg that needs to be set to _ctx.
 */
#define XLAT_SETUP_CTX_CFG(_ctx, _cfg)		(_ctx)->cfg = (_cfg)

/*
 * Set up the xlat_ctx_tbls field of a given context.
 * This macro doesn't check parameters.
 *
 * _ctx:
 *   Context where to add the configuration strucutre.
 *
 * _tlbs:
 *   Reference to the xlat_ctx_tlbs structure where to add to the context.
 */
#define XLAT_SETUP_CTX_TBLS(_ctx, _tbls)	(_ctx)->tbls = (_tbls)

/*
 * Initialize an existing xlat_ctx_tbls structure with the given parameters
 * This macro doesn't check parameters.
 *
 * _tlbs:
 *   Pointer to xlat_ctx.
 *
 * _tables:
 *   pointer to non-base xlat_ctx_tbls.
 *
 * _tnum:
 *   Maximum number of intermediate tables that can fit in the _tables area.
 *
 * _btables:
 *   pointer to base xlat_ctx_tbls.
 *
 * _bt_entries:
 *   Maximum number of entries available on the base table.
 */
#define XLAT_INIT_CTX_TBLS(_tbls, _tables, _tnum,			\
			   _btables, _bt_entries)			\
	{								\
		(_tbls)->tables = (_tables);				\
		(_tbls)->tables_num = (_tnum);				\
		(_tbls)->base_table = (_btables);			\
		(_tbls)->max_base_table_entries = (_bt_entries);	\
		(_tbls)->next_table = 0U;				\
		(_tbls)->initialized = false;				\
	}

#endif /* XLAT_TABLES_PRIVATE_H */

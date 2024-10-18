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

/*
 * Initialize translation tables associated to the current context.
 *
 * This function assumes that the xlat_ctx_cfg field of the context has been
 * properly configured by previous calls to xlat_ctx_cfg_init() and that
 * all the tables are of page size.
 *
 * This function returns 0 on success or an error code otherwise.
 */
int xlat_init_tables_ctx(struct xlat_ctx *ctx);

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
uint64_t xlat_desc(uint64_t attr, uintptr_t addr_pa, int level);

/*
 * Return the maximum physical address supported by the hardware.
 */
uintptr_t xlat_arch_get_max_supported_pa(void);

/*
 * Return the unprivileged execute-never mask that will prevent instruction
 * fetch by EL0 at the EL2&0 translation regime.
 */
#define XLAT_GET_UXN_DESC() (UPPER_ATTRS(UXN))

/*
 * Return the priviledged execute-never mask that will prevent instruction
 * fetch by EL2 at the EL2&0 translation regime.
 */
#define XLAT_GET_PXN_DESC() (UPPER_ATTRS(PXN))

/*
 * Return the Guarded Page mask that will be used by BTI.
 */
#define XLAT_GET_GP_DESC() (UPPER_ATTRS(GP))

/*
 * Return the NG flag for a page or block descriptor
 */
#define XLAT_GET_NG_HINT() (LOWER_ATTRS(NG_HINT))

/*
 * Return the AP access unprivileged for a page or block descriptor
 */
#define XLAT_GET_AP_ACCESS_UNPRIV_DESC() (LOWER_ATTRS(AP_ACCESS_UNPRIVILEGED))

/*
 * Initialize an existing xlat_ctx_tbls structure with the given parameters
 * This macro doesn't check parameters.
 *
 * _tlbs:
 *   Pointer to xlat_ctx_tlbs structure.
 *
 * _tables:
 *   pointer to a translation table array containing all the translation
 *   tables.
 *
 * _tnum:
 *   Maximum number of tables that can fit in the _tables area.
 */
#define XLAT_INIT_CTX_TBLS(_tbls, _tables, _tnum)			\
	{								\
		(_tbls)->tables = (_tables);				\
		(_tbls)->tables_num = (_tnum);				\
		(_tbls)->next_table = 0U;				\
		(_tbls)->initialized = false;				\
	}

#endif /* XLAT_TABLES_PRIVATE_H */

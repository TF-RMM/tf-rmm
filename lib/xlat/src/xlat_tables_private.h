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
 * Invalidate all TLB entries that match the given virtual address.
 * This functions must be called for every translation table entry
 * that is modified. It only affects the EL2 Translate regime.
 * _sh is `ish` or `nsh`.
 *
 * Ensure the translation table write has drained into memory
 * before invalidating the TLB entry. Note that the barrier is scoped
 * according the _sh parameter and the TLBI is also scoped.
 */

#define __TLBIVAE2ish tlbivae2is
#define __TLBIVAE2nsh tlbivae2

#define XLAT_ARCH_TLBI_VA(va, _sh) \
	do { \
		dsb(_sh##st); \
		__TLBIVAE2##_sh(TLBI_ADDR(va)); \
	} while (false)

/*
 * A macro that takes start_va, end_va, _sh, and granule_sz as arguments and
 * issues TLBI for each VA in the range [start_va, end_va):
 */
#define XLAT_ARCH_TLBI_VA_RANGE(start_va, end_va, _sh, granule_sz) \
	do { \
		dsb(_sh##st); \
		for (uintptr_t _va = (start_va); _va < (end_va); \
				_va += (granule_sz)) { \
			__TLBIVAE2##_sh(TLBI_ADDR(_va)); \
		} \
	} while (false)

/*
 * This macro has to be called at the end of any code that uses
 * XLAT_ARCH_TLBI_VA(). _sh is `ish` or `nsh`.
 *
 * A TLB maintenance instruction can complete at any time after
 * it is issued, but is only guaranteed to be complete after the
 * execution of DSB by the PE that executed the TLB maintenance
 * instruction. After the TLB invalidate instruction is
 * complete, no new memory accesses using the invalidated TLB
 * entries will be observed by any observer of the system
 * domain. See section D4.8.2 of the ARMv8 (issue k), paragraph
 * "Ordering and completion of TLB maintenance instructions".
 *
 * The effects of a completed TLB maintenance instruction are
 * only guaranteed to be visible on the PE that executed the
 * instruction after the execution of an ISB instruction by the
 * PE that executed the TLB maintenance instruction.
 */
#define XLAT_ARCH_TLBI_SYNC(_sh) \
	do { \
		dsb(_sh); \
		isb(); \
	} while (false)

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
 * Return the Alternate MECID mask for a page or block descriptor.
 */
#define XLAT_GET_AMEC_DESC() (UPPER_ATTRS(AMEC))

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
#define XLAT_INIT_CTX_TBLS(_tbls, _tables, _tnum, _base_table_pa)	\
	{								\
		(_tbls)->tables = (_tables);				\
		(_tbls)->tables_num = (_tnum);				\
		(_tbls)->next_table = 0U;				\
		(_tbls)->base_table_pa = (_base_table_pa);		\
		(_tbls)->init = false;					\
	}

#endif /* XLAT_TABLES_PRIVATE_H */

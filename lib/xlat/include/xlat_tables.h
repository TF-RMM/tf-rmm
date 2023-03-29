/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

/* This file is derived from xlat_table_v2 library in TF-A project */

#ifndef XLAT_TABLES_H
#define XLAT_TABLES_H

#ifndef __ASSEMBLER__

#include <limits.h>
#include <memory.h>
#include <stddef.h>
#include <stdint.h>

#endif

#include <xlat_contexts.h>
#include <xlat_defs.h>

#ifndef __ASSEMBLER__

/*
 * Default granularity size for a struct xlat_mmap_region.
 * Useful when no specific granularity is required.
 *
 * By default, choose the biggest possible block size allowed by the
 * architectural state and granule size in order to minimize the number of page
 * tables required for the mapping.
 */
#define REGION_DEFAULT_GRANULARITY	XLAT_BLOCK_SIZE(MIN_LVL_BLOCK_DESC)

/*
 * Helper macro to define a struct xlat_mmap_region. This macro allows to
 * specify all the fields of the structure but its parameter list is not
 * guaranteed to remain stable as we add members to struct xlat_mmap_region.
 */
#define MAP_REGION_FULL_SPEC(_pa, _va, _sz, _attr, _gr)		\
	{							\
		.base_pa = (_pa),				\
		.base_va = (_va),				\
		.size = (_sz),					\
		.attr = (_attr),				\
		.granularity = (_gr),				\
	}

/* Helper macro to define anstruct xlat_mmap_region. */
#define MAP_REGION(_pa, _va, _sz, _attr)	\
	MAP_REGION_FULL_SPEC(_pa, _va, _sz, _attr, REGION_DEFAULT_GRANULARITY)

/* Helper macro to define anstruct xlat_mmap_region with an identity mapping. */
#define MAP_REGION_FLAT(_adr, _sz, _attr)			\
	MAP_REGION(_adr, _adr, _sz, _attr)

/*
 * Helper macro to define an mmap_region_t to map with the desired granularity
 * of translation tables but with invalid page descriptors.
 *
 * The granularity value passed to this macro must be a valid block or page
 * size. When using a 4KB translation granule, this might be 4KB, 2MB or 1GB.
 * Passing REGION_DEFAULT_GRANULARITY is also allowed and means that the library
 * is free to choose the granularity for this region.
 *
 * This macro can be used to define transient regions where memory used to
 * reserve VA can be assigned to a PA dynamically. These VA will fault if it
 * is accessed before a valid PA is assigned to it.
 */

#define MAP_REGION_TRANSIENT(_va, _sz, _gr)			\
	MAP_REGION_FULL_SPEC(ULL(0), _va, _sz, MT_TRANSIENT, _gr)

/*
 * Use the first bit reserved for sofware use in the table/block upper
 * attributes field as a flag to know if a tte corresponds to a transient
 * address or not.
 */
#define TRANSIENT_FLAG_SHIFT	U(55)
#define TRANSIENT_FLAG_WIDTH	U(1)

/*
 * TRANSIENT_DESC can be used either as a bit mask or as an absolute value.
 * The absolute value is used to mark an invalid transient TTE and the mask
 * is used to mark a valid TTE as transient.
 */
#define TRANSIENT_DESC		INPLACE(TRANSIENT_FLAG, 1UL)

/*
 * Shifts and masks to access fields of an mmap attribute
 */
#define MT_TYPE_SHIFT		UL(0)
#define MT_TYPE_WIDTH		UL(4)
#define MT_TYPE_MASK		MASK(MT_TYPE)
#define MT_TYPE(_attr)		((_attr) & MT_TYPE_MASK)
/* Access permissions (RO/RW) */
#define MT_PERM_SHIFT		(MT_TYPE_SHIFT + MT_TYPE_WIDTH)
/* Access permissions for instruction execution (EXECUTE/EXECUTE_NEVER) */
#define MT_EXECUTE_FLAG_SHIFT	(MT_PERM_SHIFT + 1UL)

/* Contiguos descriptor flag */
#define MT_CONT_SHIFT		(MT_EXECUTE_FLAG_SHIFT + 1UL)

/* NG Flag */
#define MT_NG_SHIFT		(MT_CONT_SHIFT + 1UL)

/* Shareability attribute for the memory region */
#define MT_SHAREABILITY_SHIFT	(MT_NG_SHIFT + 1UL)
#define MT_SHAREABILITY_WIDTH	UL(2)
#define MT_SHAREABILITY_MASK	MASK(MT_SHAREABILITY)
#define MT_SHAREABILITY(_attr)	((_attr) & MT_SHAREABILITY_MASK)

/* Physical address space (REALM/NS, as ROOT/SECURE do not apply to R-EL2) */
#define MT_PAS_SHIFT		(MT_SHAREABILITY_SHIFT + MT_SHAREABILITY_WIDTH)
#define MT_PAS_WIDTH		UL(1)
#define MT_PAS_MASK		MASK(MT_PAS)
#define MT_PAS(_attr)		((_attr) & MT_PAS_MASK)

/* All other bits are reserved */

/* Macro to access translatio table lower attributes */
#define LOWER_ATTRS_SHIFT	(2U)
#define LOWER_ATTRS_WIDTH	(10U)
#define LOWER_ATTRS_MASK	MASK(LOWER_ATTRS)
#define LOWER_ATTRS(x)		(INPLACE(LOWER_ATTRS, x) & (LOWER_ATTRS_MASK))

/* Public definitions to use with the LOWER_ATTRS() macro*/
#define NS			(U(0x1) << UL(3))   /* Bit[5] absolutely */

/*
 * Memory mapping attributes
 */

/*
 * Memory types supported.
 * These are organised so that, going down the list, the memory types are
 * getting weaker; conversely going up the list the memory types are getting
 * stronger.
 */
#define MT_DEVICE		UL(0)
#define MT_MEMORY		UL(2)
#define MT_TRANSIENT		UL(3)
/* Values up to 7 are reserved to add new memory types in the future */

#define MT_RO			INPLACE(MT_PERM, 0UL)
#define MT_RW			INPLACE(MT_PERM, 1UL)

#define MT_REALM		INPLACE(MT_PAS, 0UL)
#define MT_NS			INPLACE(MT_PAS, 1UL)

/*
 * Access permissions for instruction execution are only relevant for normal
 * read-only memory, i.e. MT_MEMORY | MT_RO. They are ignored (and potentially
 * overridden) otherwise:
 *  - Device memory is always marked as execute-never.
 *  - Read-write normal memory is always marked as execute-never.
 */
#define MT_EXECUTE		INPLACE(MT_EXECUTE_FLAG, 0UL)
#define MT_EXECUTE_NEVER	INPLACE(MT_EXECUTE_FLAG, 1UL)

/*
 * Shareability defines the visibility of any cache changes to
 * all masters belonging to a shareable domain.
 *
 * MT_SHAREABILITY_ISH: For inner shareable domain
 * MT_SHAREABILITY_OSH: For outer shareable domain
 * MT_SHAREABILITY_NSH: For non shareable domain
 */
#define MT_SHAREABILITY_ISH	INPLACE(MT_SHAREABILITY, 1UL)
#define MT_SHAREABILITY_OSH	INPLACE(MT_SHAREABILITY, 2UL)
#define MT_SHAREABILITY_NSH	INPLACE(MT_SHAREABILITY, 3UL)

#define MT_NG			INPLACE(MT_NG, 1UL)

/* Compound attributes for most common usages */
#define MT_CODE			(MT_MEMORY | MT_SHAREABILITY_ISH \
				 | MT_RO | MT_EXECUTE)
#define MT_RO_DATA		(MT_MEMORY | MT_SHAREABILITY_ISH \
				 | MT_RO | MT_EXECUTE_NEVER)
#define MT_RW_DATA		(MT_MEMORY | MT_SHAREABILITY_ISH \
				 | MT_RW | MT_EXECUTE_NEVER)

/*
 * Structure for specifying a single region of memory.
 */
struct xlat_mmap_region {
	uintptr_t	base_pa;	/* Base PA for the current region. */
	uintptr_t	base_va;	/* Base VA for the current region. */
	size_t		size;		/* Size of the current region. */
	uint64_t	attr;		/* Attrs for the current region. */
	size_t		granularity;    /* Region granularity. */
};

/*
 * Structure containing a table entry and its related information.
 */
struct xlat_llt_info {
	uint64_t *table;	/* Pointer to the translation table. */
	uintptr_t llt_base_va;	/* Base VA that is applicable to this llt. */
	unsigned int level;	/* Table level of the current entry. */
};

/******************************************************************************
 * Generic translation table APIs.
 *****************************************************************************/

static inline void xlat_write_tte(uint64_t *entry, uint64_t desc)
{
	SCA_WRITE64(entry, desc);
}

static inline uint64_t xlat_read_tte(uint64_t *entry)
{
	return SCA_READ64(entry);
}

/*
 * Return a xlat_llt_info structure given a context and a VA.
 * The return structure is populated on the retval field.
 *
 * If 'va' is within the boundaries of the context's VA space, this function
 * will return the last level table information, regardless of whether 'va'
 * is mapped or not.
 *
 * This function returns 0 on success or a POSIX error code otherwise.
 */
int xlat_get_llt_from_va(struct xlat_llt_info * const retval,
			 const struct xlat_ctx * const ctx,
			 const uintptr_t va);

/*
 * Function to unmap a memory page for a given VA. The region to which the VA
 * belongs should have been configured as TRANSIENT during the xlat library
 * configuration.
 *
 * This function implements the "Break" part of the Break-Before-Make
 * semantics needed by the Armv8.x architecture in order to update the page
 * descriptors.
 *
 * This function returns 0 on success or an error code otherwise.
 */
int xlat_unmap_memory_page(struct xlat_llt_info * const table,
			   const uintptr_t va);

/*
 * Function to map a physical memory page from the descriptor table entry
 * and VA given. The region to which the VA belongs should have been configured
 * as TRANSIENT during the xlat library configuration.
 * This function implements the "Make" part of the
 * Break-Before-Make semantics mandated by the Armv8.x architecture in order
 * to update the page descriptors.
 *
 * This function returns 0 on success or a negative error code otherwise.
 *
 * For simplicity, this function
 *	- will not check for overlaps of the PA with other mmap regions.
 *	- will mask out the LSBs of the PA so the page/block corresponding to
 *	  the PA will actually be mapped.
 */
int xlat_map_memory_page_with_attrs(const struct xlat_llt_info * const table,
				    const uintptr_t va,
				    const uintptr_t pa,
				    const uint64_t attrs);

/*
 * This function finds the TTE on a table given the corresponding
 * xlat_llt_info structure and the VA corresponding to the entry.
 *
 * If va is outside the range for the table, it returns NULL.
 *
 * For simplicity and as long as va is applicable to the table, this function
 * will return a pointer to a tte on the table without making any asumption
 * about its type or validity. It is the caller responsibility to do any
 * necessary checks on the returned tte before using it.
 */
uint64_t *xlat_get_tte_ptr(const struct xlat_llt_info * const table,
			   const uintptr_t va);

/*
 * Set up the MMU configuration registers for the specified platform parameters.
 *
 * This function must be called for each context as it configures the
 * appropriate TTBRx register depending on it.
 *
 * This function also assumes that the contexts for high and low VA halfs share
 * the same virtual address space as well as the same physical address space,
 * so it is safe to call it for each context initialization.
 *
 * Returns 0 on success or a negative error code otherwise.
 */
int xlat_arch_setup_mmu_cfg(struct xlat_ctx * const ctx);

/* MMU control */
void xlat_enable_mmu_el2(void);

#endif /*__ASSEMBLER__*/
#endif /* XLAT_TABLES_H */

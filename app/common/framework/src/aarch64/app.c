/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <app_common.h>
#include <app_header.h>
#include <app_header_private.h>
#include <arch.h>
#include <arch_helpers.h>
#include <assert.h>
#include <buffer.h>
#include <debug.h>
#include <errno.h>
#include <granule.h>
#include <import_sym.h>
#include <utils_def.h>
#include <xlat_contexts.h>
#include <xlat_tables.h>

#define GRANULE_PA_IDX_APP_REG_CTX	0U
#define GRANULE_PA_IDX_APP_PAGE_TABLE	1U
#define GRANULE_PA_IDX_COUNT		2U

#define RMM_APP_APP_REG_CTX_MMAP_IDX	0U
#define RMM_APP_TEXT_MMAP_IDX		1U
#define RMM_APP_RODATA_MMAP_IDX		2U
#define RMM_APP_DATA_MMAP_IDX		3U
#define RMM_APP_BSS_MMAP_IDX		4U
#define RMM_APP_SHARED_IDX		5U
#define RMM_APP_HEAP_IDX		6U
#define RMM_APP_STACK_IDX		7U
#define RMM_APP_MMAP_REGION_COUNT	8U

#define ASID_SIZE_NO_FEAT_ASID16	8U

struct app_id_data {
	struct xlat_ctx_cfg app_va_xlat_ctx_cfg_base;
	struct xlat_mmap_region mm_regions_array[RMM_APP_MMAP_REGION_COUNT];
	uintptr_t el0_shared_page_va;
	uintptr_t heap_va;
	uintptr_t stack_buf_start_va;
};

static struct app_id_data app_id_data_array[APP_COUNT];

struct app_bss_memory_t {
	uintptr_t pa;
	size_t size;
};
static struct app_bss_memory_t app_bss_memory_array[APP_COUNT];

/* This function is implemented in assembly */
/* TODO: get this declarations properly from a header */
int run_app(struct app_reg_ctx *app_reg_ctx, uint64_t heap_properties);

IMPORT_SYM(uintptr_t, rmm_rw_start, RMM_RW_RANGE_START);
IMPORT_SYM(uintptr_t, rmm_rw_end, RMM_RW_RANGE_END);

static bool in_rmm_rw_range(uintptr_t address)
{
	return (address >= RMM_RW_RANGE_START) && (address < RMM_RW_RANGE_END);
}

static void *map_page_to_slot(uintptr_t pa, enum buffer_slot slot)
{
	/* See whether the pa is in the rmm RW area */
	if (in_rmm_rw_range(pa)) {
		return (void *)pa;
	}
	/* Assume delegated granule */
	struct granule *app_data_granule = find_lock_granule(pa, GRANULE_STATE_REC_AUX);

	if (app_data_granule == NULL) {
		ERROR("ERROR %s:%d\n", __func__, __LINE__);
		return NULL;
	}
	return buffer_granule_map(app_data_granule, slot);
}

static void *slot_map_app_pagetable(uintptr_t pa)
{
	return map_page_to_slot(pa, SLOT_APP_PAGE_TABLE);
}

static void *slot_map_page_to_init(uintptr_t pa)
{
	return map_page_to_slot(pa, SLOT_APP_INIT);
}

static void *slot_map_app_reg_ctx_page(uintptr_t pa)
{
	return map_page_to_slot(pa, SLOT_APP_INIT);
}

static void unmap_page(uintptr_t pa, void *va)
{
	struct granule *g;

	if (in_rmm_rw_range(pa)) {
		return;
	}
	buffer_unmap(va);
	g = find_granule(pa);
	granule_unlock(g);
}

static int init_app_translation(size_t app_id,
				struct app_data_cfg *app_data,
				uintptr_t page_table_pa,
				void *page_table)
{
	int ret;
	size_t app_index;

	if (!GRANULE_ALIGNED(page_table_pa)) {
		return -EINVAL;
	}

	ret = app_get_index(app_id, &app_index);
	if (ret != 0) {
		return ret;
	}

	/* To prevent array subscript <unknown> is outside array bounds warning */
	/* cppcheck-suppress unsignedPositive
	 * As app_index is unsigned, app_index >= APP_COUNT is always true if
	 * APP_COUNT is zero.
	 */
	/* coverity[no_effect:SUPPRESS] */
	/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
	if (app_index >= APP_COUNT) {
		return -EINVAL;
	}

	/* Copy the prepared base config into the app instance's own config */
	/* coverity[deadcode:SUPPRESS] */
	/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
	app_data->app_va_xlat_ctx_cfg = app_id_data_array[app_index].app_va_xlat_ctx_cfg_base;
	app_data->el0_shared_page_va = app_id_data_array[app_index].el0_shared_page_va;
	app_data->heap_va = app_id_data_array[app_index].heap_va;
	app_data->stack_buf_start_va = app_id_data_array[app_index].stack_buf_start_va;

	/*
	 * Initialize the translation tables for the APP.
	 */
	ret = xlat_ctx_init(&app_data->app_va_xlat_ctx,
				&app_data->app_va_xlat_ctx_cfg,
				&app_data->app_va_tbls,
				page_table,
				APP_XLAT_TABLE_COUNT);
	if (ret != 0) {
		return ret;
	}

	ret = xlat_arch_setup_mmu_cfg(&app_data->app_va_xlat_ctx, &app_data->mmu_config);
	if (ret != 0) {
		return ret;
	}

	/* TODO: The xlat library writes the VA of the base table to te TTBR.
	 * For delegated granules this VA doesn't match with the PA, so need
	 * to update the TTBR here.
	 * One change to do in future could be to change
	 * xlat_arch_setup_mmu_cfg() to take max_va, region and base table
	 * address as input and give the mmu_config as output.
	 */
	if (!in_rmm_rw_range((uintptr_t)page_table)) {
		unsigned long ttbrx = app_data->mmu_config.ttbrx;

		assert((page_table_pa & MASK(TTBRx_EL2_BADDR)) == page_table_pa);
		/* clear the bits for TTBRx_EL2_BADDR */
		ttbrx &= ~MASK(TTBRx_EL2_BADDR);
		/* write the new address */
		ttbrx |= page_table_pa;
		app_data->mmu_config.ttbrx = ttbrx;
	}

	/* Make sure that the app ID fits in the ASID field */
	assert(app_id < (1LU << ASID_SIZE_NO_FEAT_ASID16));
	/* ASID 0 is reserved to EL2 RMM */
	assert(app_id != 0U);
	/* Set the ASID field in the TTBR to the app ID */
	app_data->mmu_config.ttbrx |= INPLACE(TTBRx_EL2_ASID, app_id);

	/*
	 * TODO: This limits the max APP VA size. (i.e. a single 3rd level table
	 * is used). This is 2MB of address space. Provide a more general
	 * solution (updating the cache when mapping the pages and llt changes,
	 * etc.)
	 */
	return xlat_get_llt_from_va(&app_data->cached_app_llt_info,
					&app_data->app_va_xlat_ctx,
					APP_VA_START);
}

/* Map a page in the transient region in the APP VA space */
static int app_xlat_map(struct app_data_cfg *app_data,
			  uintptr_t va,
			  uintptr_t pa,
			  uint64_t attr)
{
	struct xlat_llt_info *entry = &app_data->cached_app_llt_info;

	assert(GRANULE_ALIGNED(pa));
	/* TODO: Some xlat_... functions assume they are modifying the
	 * in-context xlat tables (and hence does all dsb, isb) , but these are
	 * not required when modifying an out of context xlat table.
	 */
	return xlat_map_memory_page_with_attrs(entry, va, pa, attr);
}

static int allocate_bss(size_t app_id, size_t bss_size, uintptr_t *pa)
{
	/* TODO: For each application RMM should allocate the required
	 * amount of zero initialised memory (from EL3). As currently this
	 * allocation mechanism is not available, as a temporary workaround the
	 * BSS memory for an app is allocated in the app's rmm_stub library.
	 */
	size_t app_index;
	int ret;
	struct app_header *app_header;

	(void)bss_size;

	ret = app_get_index(app_id, &app_index);
	if (ret != 0) {
		return ret;
	}
	ret = app_get_header_ptr_at_index(app_index, &app_header);
	assert(ret == 0);
	assert(app_bss_memory_array[app_index].size == bss_size);
	*pa = app_bss_memory_array[app_index].pa;
	return 0;
}

size_t app_get_required_granule_count(unsigned long app_id)
{
	struct app_header *app_header;
	int ret;

	ret = app_get_header_ptr(app_id, &app_header);
	if (ret != 0) {
		return 0UL;
	}

	return app_get_required_granule_count_from_header(app_header);
}

static uintptr_t section_start_pa(uintptr_t app_header, size_t section_offset)
{
	return app_header +
	       APP_HEADER_SIZE +    /* Skip the padded app header */
	       section_offset;
}

void app_map_shared_page(struct app_data_cfg *app_data)
{
	assert(app_data->el2_shared_page == NULL);
	app_data->el2_shared_page = map_page_to_slot(app_data->shared_page_pa, SLOT_APP_SHARED);
}

void app_unmap_shared_page(struct app_data_cfg *app_data)
{
	assert(app_data->el2_shared_page != NULL);
	unmap_page(app_data->shared_page_pa, app_data->el2_shared_page);
	app_data->el2_shared_page = NULL;
}

static int app_rw_page_xlat_map(struct app_data_cfg *app_data,
	      uintptr_t va,
	      size_t section_size,
	      const char *section_name,
	      size_t *next_granule_idx,
	      uintptr_t granule_pas[],
	      size_t granule_count)
{
	size_t section_bytes_mapped;

	for (section_bytes_mapped = 0;
	     section_bytes_mapped < section_size;
	     section_bytes_mapped += GRANULE_SIZE) {
		int ret;

		if (*next_granule_idx >= granule_count) {
			return -EINVAL;
		}

		INFO("    mapping %s page: 0x%lx -> 0x%lx\n",
			section_name, granule_pas[*next_granule_idx], va);
		ret = app_xlat_map(
			app_data,
			va,
			granule_pas[*next_granule_idx],
			(MT_RW_DATA | MT_REALM | MT_AP_UNPRIV | MT_NG));
		if (ret != 0) {
			return ret;
		}
		*next_granule_idx += 1UL;
		va += GRANULE_SIZE;
	}
	return 0;

}

static int app_shared_xlat_map(struct app_data_cfg *app_data,
	       uintptr_t va,
	       size_t *next_granule_idx,
	       uintptr_t granule_pas[],
	       size_t granule_count)
{

	size_t shared_page_idx = *next_granule_idx;
	int ret;

	ret = app_rw_page_xlat_map(app_data, va, GRANULE_SIZE, ".shared",
	      next_granule_idx, granule_pas, granule_count);
	if (ret != 0) {
		return ret;
	}
	app_data->shared_page_pa = granule_pas[shared_page_idx];
	return ret;
}

static int app_stack_xlat_map(struct app_data_cfg *app_data,
	      uintptr_t va,
	      size_t stack_size,
	      size_t *next_granule_idx,
	      uintptr_t granule_pas[],
	      size_t granule_count)
{
	return app_rw_page_xlat_map(app_data, va, stack_size, ".stack",
	      next_granule_idx, granule_pas, granule_count);
}

static int app_heap_xlat_map(struct app_data_cfg *app_data,
	      uintptr_t va,
	      size_t heap_size,
	      size_t *next_granule_idx,
	      uintptr_t granule_pas[],
	      size_t granule_count)
{
	return app_rw_page_xlat_map(app_data, va, heap_size, ".heap",
	      next_granule_idx, granule_pas, granule_count);
}

int app_init_data(struct app_data_cfg *app_data,
		      unsigned long app_id,
		      uintptr_t granule_pas[],
		      size_t granule_count)
{
	struct app_header *app_header = NULL;
	int ret = 0;
	/* idx 0 and 1 is used for app_reg_ctx and for page table */;
	size_t next_granule_idx = GRANULE_PA_IDX_COUNT;
	uintptr_t stack_top;

	INFO("Initialising app %lu\n", app_id);

	if (app_data == NULL) {
		ERROR("%s (%u): app data is NULL\n", __func__, __LINE__);
		return -EINVAL;
	}

	if (app_get_header_ptr(app_id, &app_header) < 0) {
		ERROR("%s (%u): failed to get header ptr for app_id %lu:\n",
			__func__, __LINE__, app_id);
		return -EINVAL;
	}

	if (granule_count < app_get_required_granule_count(app_id)) {
		ERROR("%s (%u): Not enough RW pages: %lu instead of %lu\n",
			__func__, __LINE__, granule_count, app_get_required_granule_count(app_id));
		return -ENOMEM;
	}

	/* Initialise the app_data structure */
	(void)memset(app_data, 0, sizeof(app_data[0]));

	size_t stack_size = app_header->stack_page_count * GRANULE_SIZE;
	size_t heap_size = app_header->heap_page_count * GRANULE_SIZE;

	INFO("    stack_size = %lu\n", stack_size);
	INFO("    heap_size = %lu\n", heap_size);

	void *page_table = slot_map_app_pagetable(granule_pas[GRANULE_PA_IDX_APP_PAGE_TABLE]);

	ret = init_app_translation(
		app_id, app_data, granule_pas[GRANULE_PA_IDX_APP_PAGE_TABLE], page_table);
	if (ret != 0) {
		goto unmap_page_table;
	}

	/* Map the app_reg_ctx page to the dedicated transient region */
	ret = app_xlat_map(app_data,
			  APP_VA_START,
			  granule_pas[GRANULE_PA_IDX_APP_REG_CTX],
			  XLAT_NG_DATA_ATTR);
	if (ret != 0) {
		goto unmap_page_table;
	}

	ret = app_shared_xlat_map(app_data, app_data->el0_shared_page_va,
		&next_granule_idx, granule_pas, granule_count);
	if (ret != 0) {
		goto unmap_page_table;
	}
	ret = app_stack_xlat_map(app_data, app_data->stack_buf_start_va, stack_size,
		&next_granule_idx, granule_pas, granule_count);
	if (ret != 0) {
		goto unmap_page_table;
	}
	stack_top = app_data->stack_buf_start_va + stack_size;

	app_data->heap_size = heap_size;
	ret = app_heap_xlat_map(app_data, app_data->heap_va, app_data->heap_size,
		&next_granule_idx, granule_pas, granule_count);
	if (ret != 0) {
		goto unmap_page_table;
	}

	/* Set up register initial values for entering the app */
	app_data->entry_point = app_header->section_text_va;

	app_data->app_reg_ctx_pa = granule_pas[GRANULE_PA_IDX_APP_REG_CTX];
	struct app_reg_ctx *app_reg_ctx =
		(struct app_reg_ctx *)slot_map_page_to_init(app_data->app_reg_ctx_pa);

	if (app_reg_ctx == NULL) {
		ERROR("%s (%u): Failed to map app_reg_ctx page\n", __func__, __LINE__);
		goto unmap_page_table;
	}
	app_reg_ctx->app_ttbr1_el2 = app_data->mmu_config.ttbrx;
	app_reg_ctx->sp_el0 = stack_top;
	app_reg_ctx->pstate = SPSR_EL2_MODE_EL0t |
				       SPSR_EL2_nRW_AARCH64 |
				       SPSR_EL2_F_BIT |
				       SPSR_EL2_I_BIT |
				       SPSR_EL2_A_BIT |
				       SPSR_EL2_D_BIT;
	app_reg_ctx->pc = app_data->entry_point;
	unmap_page(app_data->app_reg_ctx_pa, app_reg_ctx);
unmap_page_table:
	unmap_page(granule_pas[GRANULE_PA_IDX_APP_PAGE_TABLE], page_table);
	return ret;
}

/* TODO:
 * Collect the bss memory addresses allocated by the app rmm stub.
 * Remove this once RMM memory allocation is sorted out.
 */
static void collect_app_bss(void)
{
}

void app_framework_setup(void)
{
	size_t app_index;
	struct app_header *app_header;
	struct app_id_data *app_id_data;

	/* coverity[misra_c_2012_rule_2_2_violation:SUPPRESS] */
	collect_app_bss();

	/* cppcheck-suppress unsignedLessThanZero
	 * As app_index is unsigned, app_index < APP_COUNT cannot be true when
	 * APP_COUNT is 0.
	 */
	/* coverity[no_effect:SUPPRESS] */
	/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
	for (app_index = 0; app_index < APP_COUNT; ++app_index) {
		/* coverity[deadcode:SUPPRESS] */
		/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
		int ret;
		uintptr_t bss_pa;

		ret = app_get_header_ptr_at_index(app_index, &app_header);
		assert(ret == 0);
		app_id_data = &app_id_data_array[app_index];

		struct xlat_mmap_region region_app_reg_ctx = MAP_REGION_TRANSIENT(
					APP_VA_START,
					GRANULE_SIZE,
					PAGE_SIZE);
		app_id_data->mm_regions_array[RMM_APP_APP_REG_CTX_MMAP_IDX] = region_app_reg_ctx;

		struct xlat_mmap_region region_text = {
			section_start_pa((uintptr_t)app_header, app_header->section_text_offset),
			app_header->section_text_va,
			app_header->section_text_size,
			MT_CODE | MT_REALM | MT_EXEC_UNPRIV | MT_NG,
			PAGE_SIZE
		};
		app_id_data->mm_regions_array[RMM_APP_TEXT_MMAP_IDX] = region_text;

		struct xlat_mmap_region region_rodata = {
			section_start_pa((uintptr_t)app_header, app_header->section_rodata_offset),
			app_header->section_rodata_va,
			app_header->section_rodata_size,
			MT_RO_DATA | MT_REALM | MT_AP_UNPRIV | MT_NG,
			PAGE_SIZE
		};
		app_id_data->mm_regions_array[RMM_APP_RODATA_MMAP_IDX] = region_rodata;

		struct xlat_mmap_region region_data = {
			section_start_pa((uintptr_t)app_header, app_header->section_data_offset),
			app_header->section_data_va,
			app_header->section_data_size,
			(MT_RW_DATA | MT_REALM | MT_AP_UNPRIV | MT_NG),
			PAGE_SIZE
		};
		app_id_data->mm_regions_array[RMM_APP_DATA_MMAP_IDX] = region_data;

		ret = allocate_bss(app_header->app_id, app_header->section_bss_size, &bss_pa);
		if (ret != 0) {
			panic();
		}
		struct xlat_mmap_region region_bss = {
			bss_pa,
			app_header->section_bss_va,
			app_header->section_bss_size,
			(MT_RW_DATA | MT_REALM | MT_AP_UNPRIV | MT_NG),
			PAGE_SIZE
		};
		app_id_data->mm_regions_array[RMM_APP_BSS_MMAP_IDX] = region_bss;

		/* Pages for sections below are allocated per instantiation of
		 * the app.
		 */
		struct xlat_mmap_region region_shared = MAP_REGION_TRANSIENT(
			app_header->section_shared_va,
			GRANULE_SIZE,
			PAGE_SIZE);
		app_id_data->mm_regions_array[RMM_APP_SHARED_IDX] = region_shared;
		app_id_data->el0_shared_page_va = region_shared.base_va;

		struct xlat_mmap_region region_heap = MAP_REGION_TRANSIENT(
			/* Additional granule offset to base_va for heap underflow protection */
			region_shared.base_va + region_shared.size + GRANULE_SIZE,
			app_header->heap_page_count * GRANULE_SIZE,
			PAGE_SIZE);
		app_id_data->mm_regions_array[RMM_APP_HEAP_IDX] = region_heap;
		app_id_data->heap_va = region_heap.base_va;

		struct xlat_mmap_region region_stack = MAP_REGION_TRANSIENT(
			/* Additional granule offset to base_va for stack overflow protection */
			region_heap.base_va + region_heap.size + GRANULE_SIZE,
			app_header->stack_page_count * GRANULE_SIZE,
			PAGE_SIZE);
		app_id_data->mm_regions_array[RMM_APP_STACK_IDX] = region_stack;
		app_id_data->stack_buf_start_va = region_stack.base_va;

		/* We are using here the same VA size that is configured for the high va
		 * range, so that we can skip setting up other registers than ttbrx_el2
		 * for mmu setup.
		 */
		ret = xlat_ctx_cfg_init(&app_id_data->app_va_xlat_ctx_cfg_base, VA_HIGH_REGION,
					app_id_data->mm_regions_array,
					RMM_APP_MMAP_REGION_COUNT,
					XLAT_HIGH_VA_SIZE);
		if (ret != 0) {
			panic();
		}
	}
}

static uint64_t encode_heap_data(unsigned long heap_va, size_t heap_size)
{
	size_t heap_page_count = heap_size / GRANULE_SIZE;

	assert((heap_va & HEAP_VA_MASK) == heap_va);
	assert((heap_page_count & HEAP_PAGE_COUNT_MASK) == heap_page_count);
	return heap_va | heap_page_count;
}

unsigned long app_run(struct app_data_cfg *app_data,
			  unsigned long app_func_id,
			  unsigned long arg0,
			  unsigned long arg1,
			  unsigned long arg2,
			  unsigned long arg3)
{
	unsigned long retval;
	unsigned long old_hcr_el2 = read_hcr_el2();
	unsigned long old_elr_el2 = read_elr_el2();
	unsigned long old_spsr_el2 = read_spsr_el2();

	write_hcr_el2(HCR_EL2_INIT);

	struct app_reg_ctx *app_reg_ctx =
		(struct app_reg_ctx *)
		slot_map_app_reg_ctx_page(app_data->app_reg_ctx_pa);

	assert(app_reg_ctx != NULL);

	write_elr_el2(app_reg_ctx->pc);
	write_spsr_el2(app_reg_ctx->pstate);

	assert(!app_data->app_entered);
	app_data->app_entered = true;

	app_reg_ctx->app_regs[0] = app_func_id;
	app_reg_ctx->app_regs[1] = arg0;
	app_reg_ctx->app_regs[2] = arg1;
	app_reg_ctx->app_regs[3] = arg2;
	app_reg_ctx->app_regs[4] = arg3;

	while (true) {
		int app_exception_code;
		unsigned long esr;

		app_exception_code = run_app(app_reg_ctx,
			encode_heap_data(app_data->heap_va, app_data->heap_size));

		app_reg_ctx->pc = read_elr_el2();
		app_reg_ctx->pstate = read_spsr_el2();

		esr = read_esr_el2();

		if ((app_exception_code == ARM_EXCEPTION_SYNC_LEL) &&
		    ((esr & MASK(ESR_EL2_EC)) == ESR_EL2_EC_SVC)) {
			/* EL0 app called SVC as expected
			 * In case of SVC, the Low 16 bits contain the imm16
			 * value of the SVC instruction executed by the app.
			 */
			/* TODO: in future an app could be pre-empted by
			 * interrupt or there could be other valid exceptions.
			 */
			uint16_t imm16 = (uint16_t)EXTRACT(ESR_EL2_ISS, esr);

			if (imm16 == APP_EXIT_CALL) {
				break;
			}
		}

		unsigned long elr_el2 = read_elr_el2();

		ERROR("Failed to return properly from the EL0 app\n");
		ERROR("    ELR_EL2 = 0x%lx\n", elr_el2);

		assert(false);
	}

	/* Return the value in X0 as EL0 app return value */
	retval = app_reg_ctx->app_regs[0];

	unmap_page(app_data->app_reg_ctx_pa, app_reg_ctx);

	assert(app_data->app_entered);
	app_data->app_entered = false;

	write_hcr_el2(old_hcr_el2);
	write_elr_el2(old_elr_el2);
	write_spsr_el2(old_spsr_el2);
	isb();

	return retval;
}

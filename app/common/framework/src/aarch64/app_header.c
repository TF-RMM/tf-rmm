/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <app_header.h>
#include <app_header_private.h>
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <stddef.h>
#include <utils_def.h>

static struct app_header *app_header_ptrs[APP_COUNT];
static uint64_t rmm_start_address;
static uint64_t rmm_core_start_address;

/* The function is called from assembly */
void app_save_rmm_entry_info(uint64_t rmm_start, uint64_t rmm_core_start);

void app_save_rmm_entry_info(uint64_t rmm_start, uint64_t rmm_core_start)
{
	if ((rmm_start == 0U) || (rmm_core_start < rmm_start)) {
		panic();
	}
	rmm_start_address = rmm_start;
	rmm_core_start_address = rmm_core_start;
}

uint64_t app_get_rmm_start(void)
{
	return rmm_start_address;
}

int app_get_index(unsigned long app_id, size_t *app_index)
{
	size_t i;

	assert(app_index != NULL);
	/* cppcheck-suppress unsignedLessThanZero
	 * As i is unsigned, i < APP_COUNT cannot be true when APP_COUNT is 0.
	 */
	/* coverity[no_effect:SUPPRESS] */
	/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
	for (i = 0; i < APP_COUNT; ++i) {
		/* coverity[deadcode:SUPPRESS] */
		/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
		if (app_header_ptrs[i]->app_id == app_id) {
			*app_index = i;
			return 0;
		}
	}
	return -EINVAL;
}

int app_get_header_ptr(unsigned long app_id, struct app_header **app_header)
{
	size_t app_index;

	assert(app_header != NULL);
	if (app_get_index(app_id, &app_index) < 0) {
		return -EINVAL;
	}

	*app_header = app_header_ptrs[app_index];

	return 0;
}

int app_get_header_ptr_at_index(unsigned long app_index, struct app_header **app_header)
{
	/* cppcheck-suppress unsignedPositive
	 * As app_index is unsigned, app_index >= APP_COUNT is always true if
	 * APP_COUNT is zero.
	 */
	/* coverity[no_effect:SUPPRESS] */
	/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
	if (app_index >= APP_COUNT) {
		return -EINVAL;
	}
	/* coverity[deadcode:SUPPRESS] */
	/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
	*app_header = app_header_ptrs[app_index];
	return 0;
}

size_t app_get_required_granule_count_from_header(struct app_header *app_header)
{
	assert(app_header != NULL);

	return app_header->stack_page_count +
	       app_header->heap_page_count +
	       1U + /* Shared page */
	       1U + /* App register context */
	       1U;  /* Page Table (assuming single page) */
}

static void dump_header(struct app_header *app_header)
{

	LOG_APP_FW("    app_header_magic: #1=%016lx, #2=%016lx\n",
		app_header->app_header_magic, app_header->app_header_magic2);
	if ((app_header->app_name[APP_NAME_BUF_SIZE - 1U] == '\0')) {
		LOG_APP_FW("    app_name               =   %s\n", app_header->app_name);
	} else {
		LOG_APP_FW("    app_name INVALID\n");
	}
	LOG_APP_FW("    app_header_version     =   0x%16x\n",
		app_header->app_header_version);
		LOG_APP_FW("    app_id                 =     %16d\n", app_header->app_id);
		LOG_APP_FW("    app_len                =   0x%16lx\n", app_header->app_len);
	LOG_APP_FW("    required granule_count =     %16lu\n\n",
		app_get_required_granule_count_from_header(app_header));

	LOG_APP_FW("    section  |   offset |               va |     size\n");
	LOG_APP_FW("    ---------|----------|------------------|---------\n");
	LOG_APP_FW("    text     | %8lx | %16lx | %8lx\n",
		app_header->section_text_offset,
		app_header->section_text_va,
		app_header->section_text_size);
	LOG_APP_FW("    rodata   | %8lx | %16lx | %8lx\n",
		app_header->section_rodata_offset,
		app_header->section_rodata_va,
		app_header->section_rodata_size);
	LOG_APP_FW("    data     | %8lx | %16lx | %8lx\n",
		app_header->section_data_offset,
		app_header->section_data_va,
		app_header->section_data_size);
	LOG_APP_FW("    bss      |      N/A | %16lx | %8lx\n",
		app_header->section_bss_va,
		app_header->section_bss_size);
	LOG_APP_FW("    shared   |      N/A | %16lx | %8lx\n",
		app_header->section_shared_va,
		GRANULE_SIZE);
	LOG_APP_FW("    stack    |      N/A |              N/A | %8lx\n",
		app_header->stack_page_count * GRANULE_SIZE);
	LOG_APP_FW("    heap     |      N/A |              N/A | %8lx\n\n",
		app_header->heap_page_count * GRANULE_SIZE);
}

static int sanity_check_header(struct app_header *app_header)
{
	if (
		/* Version */
		(app_header->app_header_version !=
			(((uint32_t)HEADER_VERSION_MAJOR << 16U) | HEADER_VERSION_MINOR)) ||
		/* App name is NULL terminated */
		(app_header->app_name[APP_NAME_BUF_SIZE - 1U] != '\0') ||
		/* Alignments */
		(!GRANULE_ALIGNED(app_header->app_len)) ||
		(!GRANULE_ALIGNED(app_header->section_text_offset)) ||
		(!GRANULE_ALIGNED(app_header->section_text_va)) ||
		(!GRANULE_ALIGNED(app_header->section_text_size)) ||
		(!GRANULE_ALIGNED(app_header->section_rodata_offset)) ||
		(!GRANULE_ALIGNED(app_header->section_rodata_va)) ||
		(!GRANULE_ALIGNED(app_header->section_rodata_size)) ||
		(!GRANULE_ALIGNED(app_header->section_data_offset)) ||
		(!GRANULE_ALIGNED(app_header->section_data_va)) ||
		(!GRANULE_ALIGNED(app_header->section_data_size)) ||
		(!GRANULE_ALIGNED(app_header->section_bss_va)) ||
		(!GRANULE_ALIGNED(app_header->section_bss_size)) ||
		(!GRANULE_ALIGNED(app_header->section_shared_va)) ||
		/* Magic */
		(app_header->app_header_magic != APP_HEADER_MAGIC) ||
		(app_header->app_header_magic2 != APP_HEADER_MAGIC) ||
		/* Section overlap / order */
		((app_header->section_text_offset + app_header->section_text_size) !=
			app_header->section_rodata_offset) ||
		((app_header->section_rodata_offset + app_header->section_rodata_size) !=
			app_header->section_data_offset) ||
		/* App va space is expected to be contiguous */
		((app_header->section_text_va + app_header->section_text_size) !=
			app_header->section_rodata_va) ||
		((app_header->section_rodata_va + app_header->section_rodata_size) !=
			app_header->section_data_va) ||
		((app_header->section_data_va + app_header->section_data_size) !=
			app_header->section_bss_va) ||
		((app_header->section_bss_va + app_header->section_bss_size) !=
			app_header->section_shared_va) ||
		/* app bin is long enough */
		((app_header->section_data_offset + app_header->section_data_size +
			APP_HEADER_SIZE) != app_header->app_len)
	) {
		return 1;
	}
	return 0;
}

void app_info_setup(void)
{
	unsigned long i;
	struct app_header *app_header = (struct app_header *)rmm_start_address;

	LOG_APP_FW("Loading apps. RMM Core start address: 0x%lx\n", rmm_core_start_address);

	/* cppcheck-suppress unsignedLessThanZero
	 * As i is unsigned, i < APP_COUNT cannot be true when APP_COUNT is 0.
	 */
	/* coverity[no_effect:SUPPRESS] */
	/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
	for (i = 0; i < APP_COUNT; ++i) {
		/* coverity[deadcode:SUPPRESS] */
		/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
		if ((uintptr_t)app_header >= (uintptr_t)rmm_core_start_address) {
			ERROR("App header overlaps with RMM binary\n");
			panic();
		}

		LOG_APP_FW("App header @%lu (at 0x%lx):\n", i, (uintptr_t)app_header);
		dump_header(app_header);

		if (sanity_check_header(app_header) != 0) {
			ERROR("App header sanity check failed\n");
			panic();
		}

		app_header_ptrs[i] = app_header;

		/* Check overflow */
		if ((UINT64_MAX - app_header->app_len) < (uintptr_t)app_header) {
			panic();
		}
		app_header = (struct app_header *)&(((char *)app_header)[app_header->app_len]);
	}

	if ((uintptr_t)app_header != (uintptr_t)rmm_core_start_address) {
		/* There are extra bytes after the last header before the
		 * rmm_entry function. Maybe there were more apps provided to
		 * the bundle app than APP_COUNT?
		 */
		ERROR("Unexpected bytes between last app and RMM Core start\n");
		panic();
	}
}

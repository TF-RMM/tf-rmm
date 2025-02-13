/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef APP_HEADER_STRUCTURES_H
#define APP_HEADER_STRUCTURES_H

#include <stddef.h>
#include <stdint.h>
#include <utils_def.h>

#define APP_NAME_BUF_SIZE	32U
#define APP_HEADER_SIZE		GRANULE_SIZE

struct app_header {
	/* When the final rmm binary is constructed, an initial bl instruction
	 * is inserted at the beginning of the img file that branches to the
	 * offset of the function rmm_entry.
	 * The first 4 bytes of the padding field is modified to hold the bl
	 * instruction. This technique allows image packing logic to avoid
	 * adding an extra 4K alignment to the overall image and keep the
	 * alignments intact.
	 * Section offsets in this structures are calculated from the byte after
	 * the page containing the header.
	 * This structure needs to match the header format in app/gen_app_bin.py
	 * file.
	 */
	uint64_t padding;

	uint64_t app_header_magic;
	uint32_t app_header_version;
	const char app_name[APP_NAME_BUF_SIZE]; /* Null terminated string */
	uint32_t app_id;
	uint64_t app_len; /* including header */

	uintptr_t section_text_offset;
	uintptr_t section_text_va;
	size_t section_text_size;

	uintptr_t section_rodata_offset;
	uintptr_t section_rodata_va;
	size_t section_rodata_size;

	uintptr_t section_data_offset;
	uintptr_t section_data_va;
	size_t section_data_size;

	/* Following are not allocated in the bin */
	uintptr_t section_bss_va;
	size_t section_bss_size;

	uintptr_t section_shared_va;

	size_t stack_page_count;

	size_t heap_page_count;

	/* Reserve a few dwords for later extending the header */
	uint64_t reserved[10];

	uint64_t app_header_magic2;
};
COMPILER_ASSERT(sizeof(struct app_header) <= APP_HEADER_SIZE);

#endif /* APP_HEADER_STRUCTURES_H */

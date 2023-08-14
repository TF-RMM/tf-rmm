/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <sizes.h>

#if ((RMM_NUM_PAGES_PER_STACK == 0) || (GRANULE_SIZE == 0) || (MAX_CPUS== 0))
#error "Required config options not set for the linker script."
#endif

ENTRY(rmm_entry)

MEMORY {
	RAM (rwx): ORIGIN = 0x0, LENGTH = RMM_MAX_SIZE
}

SECTIONS
{
	rmm_base = .;

	.text . : {
		rmm_text_start = .;
		*head.S.obj(.text*)
		. = ALIGN(8);
		*(.text*)
		. = ALIGN(GRANULE_SIZE);
	} >RAM

	rmm_text_end = .;

	ASSERT(rmm_text_end == ALIGN(GRANULE_SIZE), "rmm_text_end is not page aligned")

	.rodata ALIGN(GRANULE_SIZE) : {
		rmm_ro_start = .;
		*(.rodata*)
		. = ALIGN(8);
		rmm_got_start = .;
		*(.got)
		rmm_got_end = .;
	} >RAM

	/*
	 * The xlat_static_table section is for full, aligned page tables.
	 * The static tables must not change once the MMU is enabled, so
	 * allocate them on the RO area to keep them protected from writing.
	 *
	 * The memory will be cleared by the xlat library during start up.
	 */
	xlat_table ALIGN(GRANULE_SIZE) : {
		*(xlat_static_tables)
	} >RAM

	rmm_ro_end = .;

	ASSERT(rmm_ro_end == ALIGN(GRANULE_SIZE), "rmm_ro_end is not page aligned")

	/* Align rw data to the next 2MB block */
	.data ALIGN(SZ_2M) : {
		rmm_rw_start = .;
		*(.data*)
	} >RAM

	/*
	 * .rela.dyn needs to come after .data for the read-elf utility to
	 * parse this section correctly.
	 */
	.rela.dyn ALIGN(8) : {
		rmm_rela_start = .;
		*(.rela*)
		rmm_rela_end = .;
	} >RAM

	.bss ALIGN(16) (NOLOAD) : {
		bss_start = .;
		*(.bss*)
		bss_end = .;
	} >RAM

	. = ALIGN(GRANULE_SIZE);
	rmm_rw_end = .;

	ASSERT(rmm_rw_end == ALIGN(GRANULE_SIZE), "rmm_rw_end is not page aligned")

	.stack ALIGN(GRANULE_SIZE) (NOLOAD) : {
		rmm_stack_start = .;
		. = . + (RMM_NUM_PAGES_PER_STACK * GRANULE_SIZE * MAX_CPUS);
		rmm_stack_end = .;
		rmm_eh_stack_start = .;
		. = . + (GRANULE_SIZE * MAX_CPUS);
		rmm_eh_stack_end = .;
	} >RAM

	rmm_end = .;

	ASSERT(rmm_end == ALIGN(GRANULE_SIZE), "rmm_end is not page aligned")

	/DISCARD/ : { *(.dynstr*) }
	/DISCARD/ : { *(.dynsym*) }
	/DISCARD/ : { *(.dynamic*) }
	/DISCARD/ : { *(.hash*) }
	/DISCARD/ : { *(.plt*) }
	/DISCARD/ : { *(.interp*) }
	/DISCARD/ : { *(.gnu*) }
	/DISCARD/ : { *(.note*) }
}

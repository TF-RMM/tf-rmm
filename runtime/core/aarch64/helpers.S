/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <asm_macros.S>
#include <xlat_defs.h>

	.globl	fixup_gdt_reloc

/* ---------------------------------------------------------------------------
 * Helper to fixup Global Descriptor table (GDT) and dynamic relocations
 * (.rela.dyn) at runtime.
 *
 * This function is meant to be used when the firmware is compiled with -fpie
 * and linked with -pie options. We rely on the linker script exporting
 * appropriate markers for start and end of the section. For Global Offset
 * Table (GOT), we expect 'rmm_got_start' and 'rmm_got_end' symbols to be
 * defined. Similarly for *.rela.dyn, we expect rmm_rela_start and rmm_rela_end
 * to be defined. We also expect `rmm_base` and `rmm_end` symbols to be
 * defined by the linker script and are 4KB aligned. The RMM should be
 * statically linked to start at 0x0.
 *
 * Clobber list: x0 to x7.
 * ---------------------------------------------------------------------------
 */

/* Relocation codes */
#define R_AARCH64_NONE		0
#define R_AARCH64_RELATIVE	1027

func fixup_gdt_reloc
	/* Lower Limit for fixup */
	mov	x0, xzr
	/* rmm_base and rmm_end are 4KB aligned hence adrp is enough */
	adrp	x2, rmm_base
	adrp	x1, rmm_end
	/* Upper Limit for fixup (rmm_end - rmm_base) */
	sub	x1, x1, x2

	/*
	 * Since RMM will be compiled to start at 0x0, the current
         * PC relative `rmm_base` loaded in x2 will be the Diff(S)
	 * to be applied to the fixups.
	 */
	cbz	x2, 4f	/* Diff(S) = 0. No relocation needed */

	adrp	x6, rmm_got_start
	add	x6, x6, :lo12:rmm_got_start
	adrp	x7, rmm_got_end
	add	x7, x7, :lo12:rmm_got_end

	/*
	 * GOT is an array of 64_bit addresses which must be fixed up as
	 * new_addr = old_addr + Diff(S).
	 * The new_addr is the address currently the binary is executing from
	 * and old_addr is the address at compile time.
	 */
1:	ldr	x3, [x6]
	/* Skip adding offset if address is < lower limit */
	cmp	x3, x0
	b.lo	2f

	/* Skip adding offset if address is > upper limit */
	cmp	x3, x1
	b.hi	2f
	add	x3, x3, x2
	str	x3, [x6]

2:	add	x6, x6, #8
	cmp	x6, x7
	b.lo	1b

	/* Starting dynamic relocations */
3:	adrp	x6, rmm_rela_start
	add	x6, x6, :lo12:rmm_rela_start
	adrp	x7, rmm_rela_end
	add	x7, x7, :lo12:rmm_rela_end

	/*
	 * According to ELF-64 specification, the RELA data structure is as
	 * follows:
	 *	typedef struct {
	 *		Elf64_Addr r_offset;
	 *		Elf64_Xword r_info;
	 *		Elf64_Sxword r_addend;
	 *	} Elf64_Rela;
	 *
	 * r_offset is address of reference
	 * r_info is symbol index and type of relocation (in this case
	 * code 1027 which corresponds to R_AARCH64_RELATIVE).
	 * r_addend is constant part of expression.
	 *
	 * Size of Elf64_Rela structure is 24 bytes.
	 */

1:	ldr	x3, [x6, #8]	/* r_info */
	/* Skip R_AARCH64_NONE entry with code 0 */
	cbz	x3, 2f

#ifndef NDEBUG
	/* Assert that the relocation type is R_AARCH64_RELATIVE */
	cmp	x3, #R_AARCH64_RELATIVE
	ASM_ASSERT eq
#endif
	ldr	x4, [x6, #16]	/* r_addend */

	/* Skip adding offset if r_addend is < lower limit */
	cmp	x4, x0
	b.lo	2f

	/* Skip adding offset if r_addend entry is > upper limit */
	cmp	x4, x1
	b.hi	2f

	ldr	x3, [x6]	/* r_offset */
	add	x4, x4, x2	/* Diff(S) + r_addend */
	str	x4, [x3, x2]

2:	add	x6, x6, #24
	cmp	x6, x7
	b.lo	1b

4:
	ret
endfunc fixup_gdt_reloc

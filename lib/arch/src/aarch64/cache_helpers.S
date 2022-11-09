/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <asm_macros.S>

	.globl	flush_dcache_range
	.globl	clean_dcache_range
	.globl	inv_dcache_range

/*
 * This macro can be used for implementing various data cache operations `op`
 */
.macro do_dcache_maintenance_by_mva op
	/* Exit early if size is zero */
	cbz	x1, exit_loop_\op
	dcache_line_size x2, x3
	add	x1, x0, x1
	sub	x3, x2, #1
	bic	x0, x0, x3
loop_\op:
	dc	\op, x0
	add	x0, x0, x2
	cmp	x0, x1
	b.lo	loop_\op
	dsb	sy
exit_loop_\op:
	ret
.endm
	/* ------------------------------------------
	 * Clean+Invalidate from base address till
	 * size. 'x0' = addr, 'x1' = size
	 * ------------------------------------------
	 */
func flush_dcache_range
	do_dcache_maintenance_by_mva civac
endfunc flush_dcache_range

	/* ------------------------------------------
	 * Clean from base address till size.
	 * 'x0' = addr, 'x1' = size
	 * ------------------------------------------
	 */
func clean_dcache_range
	do_dcache_maintenance_by_mva cvac
endfunc clean_dcache_range

	/* ------------------------------------------
	 * Invalidate from base address till
	 * size. 'x0' = addr, 'x1' = size
	 * ------------------------------------------
	 */
func inv_dcache_range
	do_dcache_maintenance_by_mva ivac
endfunc inv_dcache_range

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <asm_macros.S>

.section ".text"

/*
 * The following addresses are registered with the exception handler:
 */
.global ns_read
.global ns_write

.global memcpy_ns_read
.global memcpy_ns_write
.global ns_access_ret_0

/*
 * Copy data from NS into Realm memory.
 * The function returns 1 if the copy succeeds.
 * If the access to the NS memory generates a GPF, the exception handler
 * returns to ns_access_ret_0 and 0 is returned to the caller.
 * In case of failure (when 0 is returned), partial data may have been
 * written to the destination buffer
 *
 * x0 - The address of buffer in Realm memory to write into
 * x1 - The address of buffer in NS memory to read from.
 * x2 - The number of bytes to read in bytes.
 * All arguments must be aligned to 8 bytes.
 */
func memcpy_ns_read
	cbz	x2, 2f
	mov	x3, #0
1:
ns_read:
	ldr	x4, [x1], #8
	str	x4, [x0], #8
	add	x3, x3, #8
	cmp	x3, x2
	bne	1b
2:
	mov	x0, #1
	ret
endfunc memcpy_ns_read

/*
 * Copy data from Realm into NS memory.
 * The function returns 1 if the copy succeeds.
 * If the access to the NS memory generates a GPF, the exception handler
 * returns to ns_access_ret_0 and 0 is returned to the caller.
 * In case of failure (when 0 is returned), partial data may have been
 * written to the destination buffer
 *
 * x0 - The address of buffer in NS memory to write into
 * x1 - The address of buffer in Realm memory to read from.
 * x2 - The number of bytes to write.
 * All arguments must be aligned to 8 bytes.
 */
func memcpy_ns_write
	cbz	x2, 2f
	mov	x3, #0
1:
	ldr	x4, [x1], #8
ns_write:
	str	x4, [x0], #8
	add	x3, x3, #8
	cmp	x3, x2
	bne	1b
2:
	mov	x0, #1
	ret
endfunc memcpy_ns_write

func ns_access_ret_0
	mov	x0, #0
	ret
endfunc ns_access_ret_0

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef STATUS_H
#define STATUS_H

#include <assert.h>
#include <smc-rmi.h>
#include <stdbool.h>

/*
 * Logical representation of return code returned by RMM commands.
 * Each failure mode of a given command should return a unique return code, so
 * that the caller can use it to unambiguously identify the failure mode.  To
 * avoid having a very large list of enumerated values, the return code is
 * composed of a status which identifies the category of the error (for example,
 * an address was misaligned), and an index which disambiguates between multiple
 * similar failure modes (for example, a command may take multiple addresses as
 * its input; the index identifies _which_ of them was misaligned).
 *
 * Refer to smc-rmi.h for status error codes and their meanings.
 */
typedef struct {
	unsigned int status;
	unsigned int index;
} return_code_t;

/*
 * Convenience function for creating a return_code_t.
 */
static inline return_code_t make_return_code(unsigned int status,
					     unsigned int index)
{
	return (return_code_t){(unsigned int)status, index};
}

/*
 * Pack a return_code_t into a binary format, suitable for storing in a
 * register before exit from the RMM.
 */
static inline unsigned long pack_struct_return_code(return_code_t return_code)
{
	return ((unsigned long)(return_code.index) << 8) | return_code.status;
}

/*
 * Pack a return code into a binary format, suitable for storing in a register
 * on exit from the RMM.
 */
static inline unsigned long pack_return_code(unsigned int status, unsigned int index)
{
	/* The width of @status and @index is 8 bits */
	assert((status < RMI_ERROR_COUNT) && (index <= 0xffU));
	return pack_struct_return_code(make_return_code(status, index));
}

/*
 * Unpacks a return code.
 */
static inline return_code_t unpack_return_code(unsigned long error_code)
{
	return make_return_code(error_code & 0xffU, error_code >> 8);
}

#define MAX_ERR 4095

/*
 * Cast a status value to a pointer.
 */
static inline void *status_ptr(unsigned int status)
{
	return (void *)(-1 * (long)status);
}

/*
 * Check whether a pointer value represents an error.
 */
static inline bool ptr_is_err(const void *ptr)
{
	return (unsigned long)ptr >= (unsigned long)(-MAX_ERR);
}

/*
 * Cast a pointer to a status value.
 */
static inline unsigned int ptr_status(const void *ptr)
{
	assert((unsigned int)(-1 * (long)ptr) < RMI_ERROR_COUNT);
	return (unsigned int)(-1 * (long)ptr);
}

#endif /* STATUS_H */

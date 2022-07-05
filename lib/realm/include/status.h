/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef STATUS_H
#define STATUS_H

#include <stdbool.h>

/*
 * Status codes which can be returned from RMM commands.
 *
 * For each code, the meaning of return_code_t::index is stated.
 */
typedef enum {
	/*
	 * Command completed successfully.
	 *
	 * index is zero.
	 */
	RMI_SUCCESS = 0,

	/*
	 * The value of a command input value caused the command to fail.
	 *
	 * index is zero.
	 */
	RMI_ERROR_INPUT = 1,

	/*
	 * An attribute of a Realm does not match the expected value.
	 *
	 * index varies between usages.
	 */
	RMI_ERROR_REALM = 2,

	/*
	 * An attribute of a REC does not match the expected value.
	 *
	 * index is zero.
	 */
	RMI_ERROR_REC = 3,

	/*
	 * An RTT walk terminated before reaching the target RTT level,
	 * or reached an RTTE with an unexpected value.
	 *
	 * index: RTT level at which the walk terminated
	 */
	RMI_ERROR_RTT = 4,

	/*
	 * An operation cannot be completed because a resource is in use.
	 *
	 * index is zero.
	 */
	RMI_ERROR_IN_USE = 5,

	RMI_ERROR_COUNT
} status_t;

/*
 * Logical representation of return code returned by RMM commands.
 * Each failure mode of a given command should return a unique return code, so
 * that the caller can use it to unambiguously identify the failure mode.  To
 * avoid having a very large list of enumerated values, the return code is
 * composed of a status which identifies the category of the error (for example,
 * an address was misaligned), and an index which disambiguates between multiple
 * similar failure modes (for example, a command may take multiple addresses as
 * its input; the index identifies _which_ of them was misaligned.)
 */
typedef struct {
	status_t status;
	unsigned int index;
} return_code_t;

/*
 * Convenience function for creating a return_code_t.
 */
static inline return_code_t make_return_code(unsigned int status,
					     unsigned int index)
{
	return (return_code_t) {(status_t)status, index};
}

/*
 * Pack a return_code_t into a binary format, suitable for storing in a
 * register before exit from the RMM.
 */
static inline unsigned long pack_struct_return_code(return_code_t return_code)
{
	return (unsigned long)(return_code.status | (return_code.index << 8));
}

/*
 * Pack a return code into a binary format, suitable for storing in a register
 * on exit from the RMM.
 */
static inline unsigned long pack_return_code(unsigned int status, unsigned int index)
{
	/* The width of @status and @index is 8 bits */
	assert((status <= 0xffU) && (index <= 0xffU));
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
static inline void *status_ptr(status_t status)
{
	return (void *)(-1 * (unsigned long)status);
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
static inline status_t ptr_status(const void *ptr)
{
	return (status_t)(-1 * (unsigned long)ptr);
}

#endif /* STATUS_H */

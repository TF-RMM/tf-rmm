/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_SUPPORT_H
#define HOST_SUPPORT_H

#include <types.h>

/* Maximum number of sysregs for which we can install callbacks */
#define SYSREG_MAX_CBS		(30U)

/* Maximum size allowed for a sysreg name */
#define MAX_SYSREG_NAME_LEN	(25U)

/*
 * Callback prototype invoked when a sysreg is read.
 *
 * Arguments:
 *	reg - Pointer to the emulated register
 *
 * Returns:
 *	Value read from the emulated sysreg
 */
typedef u_register_t (*rd_cb_t)(u_register_t *reg);

/*
 * Callback prototype invoked when a sysreg is written.
 *
 * Arguments:
 *	val - Value to be written to the sysreg
 *	reg - Pointer to the emulated sysreg
 *
 * Returns:
 *	Void
 */
typedef void (*wr_cb_t)(u_register_t val, u_register_t *reg);

/*
 * Structure to hold the callback pointers for register access emulation.
 */
struct sysreg_cb {
	rd_cb_t rd_cb;
	wr_cb_t wr_cb;
	/*
	 * Pointer to the instance of the register corresponding to the
	 * current CPU
	 */
	u_register_t *reg;
};

/*
 * Structure to hold register access emulation data.
 */
struct sysreg_data {
	char name[MAX_SYSREG_NAME_LEN + 1U];
	struct sysreg_cb callbacks;
	u_register_t value[MAX_CPUS];
};

/*
 * Return the callbacks for a given sysreg or NULL
 * if no callbacks are found.
 *
 * Arguments:
 *	name - String containing the name of the sysreg. The name cannot exceed
 *	       MAX_SYSREG_NAME_LEN (excluding the terminatig NULL character)
 *	       or it will be truncated.
 */
struct sysreg_cb *host_util_get_sysreg_cb(char *name);

#endif /* HOST_SUPPORT_H */

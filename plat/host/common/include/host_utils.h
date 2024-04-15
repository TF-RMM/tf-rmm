/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_UTILS_H
#define HOST_UTILS_H

#include <stddef.h>
#include <types.h>

/***********************************************************************
 * Utility functions to be used across different host platform variants.
 **********************************************************************/

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

/*
 * Setup callbacks for sysreg read and write operations.
 *
 * This API allows to setup callbacks for each sysreg to be called upon
 * read or write operations. This allows to control what to return on
 * a read or how to process a write.
 *
 * Arguments:
 *	name - String containing the name of the sysreg. The name of
 *	       the sysreg cannot exceed MAX_SYSREG_NAME_LEN (excluding
 *	       the terminating NULL character) or it will be truncated.
 *	rd_cb - Callback to be invoked on a read operation.
 *	wr_cb - Callback to be invoked on a write operation.
 *	init - Value used as reset value for the sysreg.
 *
 * Returns:
 *	0 on success or a negative error code otherwise.
 */
int host_util_set_sysreg_cb(char *name, rd_cb_t rd_cb, wr_cb_t wr_cb,
			    u_register_t init);

/*
 * Setup generic callbacks for sysreg read and write operations.
 *
 * This API allows to setup generic callbacks for each sysreg to be called upon
 * read or write operations.
 *
 * Arguments:
 *	name - String containing the name of the sysreg. The name of
 *	       the sysreg cannot exceed MAX_SYSREG_NAME_LEN (excluding
 *	       the terminating NULL character) or it will be truncated.
 *	init - Value used as reset value for the sysreg.
 *
 * Returns:
 *	0 on success or a negative error code otherwise.
 */
int host_util_set_default_sysreg_cb(char *name, u_register_t init);

/*
 * Save the sysreg state across all PEs in the system along with registered
 * callbacks. This function must only be used during RMM runtime bring-up,
 * at a point wherein the system is initialized properly and can restored
 * for later test iterations.
 */
void host_util_take_sysreg_snapshot(void);

/*
 * Restore a saved sysreg state and associated callbacks. The state is already
 * assumed to be saved prior to calling this API.
 */
void host_util_restore_sysreg_snapshot(void);

/*
 * Zero all sysreg values and unregister all sysreg callbacks.
 */
void host_util_zero_sysregs_and_cbs(void);

/*
 * Return the configured address for the granule base.
 */
unsigned long host_util_get_granule_base(void);

/*
 * Set the current CPU emulated by the platform.
 */
void host_util_set_cpuid(unsigned int cpuid);

/*
 * Return the address of the EL3 RMM shared buffer.
 */
unsigned char *host_util_get_el3_rmm_shared_buffer(void);

/*
 * Performs some initialization needed before RMM can be run, such as
 * setting up callbacks for sysreg access.
 */
void host_util_setup_sysreg_and_boot_manifest(void);

/*
 * Runs the realm entrypoint as programmed in elr_el2 and resets
 * the esr_el2 before entering the Realm.
 */
int host_util_rec_run(unsigned long *regs);

/* Prototype for Realm entrypoint */
typedef int (*realm_entrypoint_t)(unsigned long *);

/* Helper for invoking RSI calls */
int host_util_rsi_helper(realm_entrypoint_t ep);

#endif /* HOST_UTILS_H */

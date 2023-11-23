/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RMM_EL3_IFC_PRIV_H
#define RMM_EL3_IFC_PRIV_H

/*
 * Function to process the boot manifest.
 *
 * Args:	None.
 * Return:	- This function does not return any value, but it will never
 *		  exit if there is an error.
 *
 * NOTE:	This function must be called with the MMU disabled.
 * NOTE2:	At return, the plat_data field of the manifest local copy
 *		will be pointing to the platform manifest in the shared area
 *		(if a platform manifest was loaded by EL3). Platform code is
 *		responsible for processing the platform manifest and keeping a
 *		local copy of it if needed at runtime.
 */
void rmm_el3_ifc_process_boot_manifest(void);

/* Platform parameter */
extern uintptr_t rmm_shared_buffer_start_va;

#endif /* RMM_EL3_IFC_PRIV_H */

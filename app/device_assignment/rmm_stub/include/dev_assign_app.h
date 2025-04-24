/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef DEV_ASSIGN_APP_H
#define DEV_ASSIGN_APP_H

#include <dev_assign_structs.h>


/*
 * Initialize an instance of device_assignment app.
 *
 * Arguments:
 * app_data - Pointer to app_data_cfg. This is uninitialized and opaque to caller
 * granule_pas - Array of contiguous granule addresses to be used for the app.
 * granule_pa_count - Num of elements in `granule_pas` array.
 * granule_va_start - Start VA address of the `granule_pas` array.
 * params - Pointer to the dev_assign_params populated by the caller.
 *
 * Returns DEV_ASSIGN_STATUS_SUCCESS on success, DEV_ASSIGN_STATUS_ERROR
 * on error.
 */
int dev_assign_app_init(struct app_data_cfg *app_data, uintptr_t granule_pas[],
	size_t granule_pa_count, void *granule_va_start,
	struct dev_assign_params *params);

#endif /* DEV_ASSIGN_APP_H */

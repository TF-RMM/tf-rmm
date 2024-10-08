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


/*
 * Communicate with device and continue the device command as part of
 * device assignment sequence.
 * Arguments:
 * app_data - Pointer to app_data_cfg. This is opaque to caller
 * comm_enter_args - Entry arguments to app
 * comm_exit_args - Exit arguments from app
 * dev_cmd - Valid device communicate cmds.
 *
 * Note that when this function indicates that the app is yeilded
 * then the only valid dev_cmd is DEVICE_ASSIGN_APP_FUNC_ID_RESUME.
 *
 * Returns DEV_ASSIGN_STATUS_SUCCESS if cmd is successful.
 *         DEV_ASSIGN_STATUS_ERROR if cmd is unsuccessful
 *         DEV_ASSIGN_STATUS_COMM_BLOCKED if the app is yielded.
 */
int dev_assign_dev_communicate(struct app_data_cfg *app_data,
	struct rmi_dev_comm_enter *comm_enter_args,
	struct rmi_dev_comm_exit *comm_exit_args,
	int dev_cmd);

/*
 * Aborts the current communication with the device.
 * Arguments:
 * app_data - Pointer to app_data_cfg. This is opaque to caller
 *
 * This command updates the status field of the struct rmi_dev_comm_enter
 * is going to be read by spdm_send_message. The value is set to error, and the
 * app is resumed, which causes the app to abort the operation and return with
 * error.
 *
 * Returns DEV_ASSIGN_STATUS_SUCCESS.
 */
int dev_assign_abort_app_operation(struct app_data_cfg *app_data);

#endif /* DEV_ASSIGN_APP_H */

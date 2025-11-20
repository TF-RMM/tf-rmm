/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

 #include <app.h>
 #include <assert.h>
 #include <dev_assign_app.h>
 #include <dev_assign_structs.h>

/* Add declaration to prevent static checker error */
void dev_assign_app_get_bss(uintptr_t *bss_pa, size_t *bss_size);

void dev_assign_app_get_bss(uintptr_t *bss_pa, size_t *bss_size)
{
	static char dev_assign_app_bss[GRANULE_SIZE * 3U] __aligned(GRANULE_SIZE);
	*bss_pa = (uintptr_t)dev_assign_app_bss;
	*bss_size = sizeof(dev_assign_app_bss);
}

int dev_assign_app_init(struct app_data_cfg *app_data, uintptr_t granule_pas[],
	size_t granule_pa_count, void *granule_va_start,
	struct dev_assign_params *params)
{
	int rc;
	struct dev_assign_params *shared;


	rc = app_init_data(app_data,
				  RMM_DEV_ASSIGN_APP_ID,
				  granule_pas,
				  granule_pa_count,
				  granule_va_start);
	if (rc != 0) {
		return DEV_ASSIGN_STATUS_ERROR;
	}

	app_map_shared_page(app_data);
	assert(app_data->el2_shared_page != NULL);
	shared = app_data->el2_shared_page;
	(void)memcpy(shared, params, sizeof(*shared));

	rc = (int)app_run(app_data, DEVICE_ASSIGN_APP_FUNC_ID_INIT,
			app_data->heap_size, 0, 0, 0);
	assert(app_data->exit_flag == APP_EXIT_SVC_EXIT_FLAG);
	app_unmap_shared_page(app_data);

	return rc;
}

int dev_assign_dev_communicate(struct app_data_cfg *app_data,
			struct rmi_dev_comm_enter *comm_enter_args,
			struct rmi_dev_comm_exit *comm_exit_args,
			struct dev_tdisp_params *tdisp_params,
			struct dev_meas_params *meas_params,
			int dev_cmd)
{
	int rc;
	struct dev_comm_enter_shared *shared;
	struct dev_assign_op_params *shared_op_params;
	struct dev_comm_exit_shared *shared_ret;
	struct dev_assign_op_params *shared_ret_op_params;

	assert((dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_RESUME) ||
		(dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_CONNECT_INIT) ||
		(dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_STOP_CONNECTION) ||
		(dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_SECURE_SESSION) ||
		(dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_GET_MEASUREMENTS) ||
		(dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_VDM_TDISP_LOCK) ||
		(dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_VDM_TDISP_REPORT) ||
		(dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_VDM_TDISP_START) ||
		(dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_VDM_TDISP_STOP) ||
		(dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_IDE_RESET) ||
		(dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_IDE_REFRESH));

	assert(app_data->el2_shared_page != NULL);
	shared = app_data->el2_shared_page;
	shared_op_params = &shared->dev_assign_op_params;
	shared->rmi_dev_comm_enter = *comm_enter_args;

	assert((tdisp_params == NULL) || (meas_params == NULL));

	if (tdisp_params != NULL) {
		struct dev_assign_tdisp_params *shared_tdisp_params =
			&shared_op_params->tdisp_params;

		shared_op_params->param_type = DEV_ASSIGN_OP_PARAMS_TDISP;
		shared_tdisp_params->tdi_id = tdisp_params->tdi_id;
		/* TODO: Is the nonce size always fixed? */
		if (tdisp_params->start_interface_nonce != NULL) {
			(void)memcpy(shared_tdisp_params->start_interface_nonce_buffer,
				     tdisp_params->start_interface_nonce,
				     RDEV_START_INTERFACE_NONCE_SIZE);
			shared_tdisp_params->nonce_ptr_is_valid = true;
		} else {
			shared_tdisp_params->nonce_ptr_is_valid = false;
		}
	} else if (meas_params != NULL) {
		shared_op_params->param_type = DEV_ASSIGN_OP_PARAMS_MEAS;
		/* Copy over measurement parameters */
		shared_op_params->meas_params = *meas_params;
	} else {
		shared_op_params->param_type = DEV_ASSIGN_OP_PARAMS_NONE;
	}

	if (dev_cmd != DEVICE_ASSIGN_APP_FUNC_ID_RESUME) {
		rc = (int)app_run(app_data, (unsigned long)dev_cmd,
				0, 0, 0, 0);
	} else {
		rc = (int)app_resume(app_data);
	}

	if (app_data->exit_flag == APP_EXIT_SVC_YIELD_FLAG) {
		rc = DEV_ASSIGN_STATUS_COMM_BLOCKED;
	}

	assert(app_data->el2_shared_page != NULL);
	shared_ret = app_data->el2_shared_page;
	shared_ret_op_params = &shared_ret->dev_assign_op_params;

	*comm_exit_args = shared_ret->rmi_dev_comm_exit;


	if (tdisp_params != NULL) {
		assert(shared_ret_op_params->param_type == DEV_ASSIGN_OP_PARAMS_TDISP);
		struct dev_assign_tdisp_params *shared_ret_tdisp_params =
			&shared_ret_op_params->tdisp_params;

		if ((tdisp_params->start_interface_nonce != NULL) &&
		    (shared_ret_tdisp_params->nonce_is_output)) {
			/* TODO: Is the nonce size always fixed? */
			(void)memcpy(tdisp_params->start_interface_nonce,
				     shared_ret_tdisp_params->start_interface_nonce_buffer,
				     RDEV_START_INTERFACE_NONCE_SIZE);
		}
	}
	/*
	 * In case of get_measurement operation (DEV_ASSIGN_OP_PARAMS_MEAS)
	 * there's nothing to do on the exit path.
	 */

	return rc;
}

int dev_assign_abort_app_operation(struct app_data_cfg *app_data)
{
	unsigned long rc __unused;
	struct rmi_dev_comm_enter *shared;

	/*
	 * The app copies the enter_args from the shared page. So set the status
	 * on the shared page to error, which will result app return
	 * immediately, unwinding its stack, and returning error.
	 */
	app_map_shared_page(app_data);
	assert(app_data->el2_shared_page != NULL);
	shared = app_data->el2_shared_page;
	shared->status = (unsigned char)RMI_DEV_COMM_ENTER_STATUS_ERROR;
	rc = app_resume(app_data);
	assert(rc == (unsigned long)DEV_ASSIGN_STATUS_ERROR);
	app_unmap_shared_page(app_data);

	return DEV_ASSIGN_STATUS_SUCCESS;
}

int dev_assign_set_public_key(struct app_data_cfg *app_data,
			      struct rmi_public_key_params *pubkey_params)
{
	int rc;

	app_map_shared_page(app_data);
	assert(app_data->el2_shared_page != NULL);
	(void)memcpy(app_data->el2_shared_page, (void *)pubkey_params,
		     sizeof(*pubkey_params));
	rc = (int)app_run(app_data, DEVICE_ASSIGN_APP_FUNC_SET_PUBLIC_KEY,
				pubkey_params->algo, 0, 0, 0);
	app_unmap_shared_page(app_data);
	return rc;
}

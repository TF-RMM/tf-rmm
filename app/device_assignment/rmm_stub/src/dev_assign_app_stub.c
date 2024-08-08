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
	static char dev_assign_app_bss[GRANULE_SIZE] __aligned(GRANULE_SIZE);
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
			struct dev_obj_digest *comm_digest_ptr,
			int dev_cmd)
{
	int rc;
	struct rmi_dev_comm_enter *shared;
	struct dev_comm_exit_shared *shared_ret;

	assert((dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_RESUME) ||
		(dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_CONNECT_INIT) ||
		(dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_STOP_CONNECTION) ||
		(dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_SECURE_SESSION));

	app_map_shared_page(app_data);
	shared = app_data->el2_shared_page;
	*shared = *comm_enter_args;

	if (dev_cmd != DEVICE_ASSIGN_APP_FUNC_ID_RESUME) {
		rc = (int)app_run(app_data, (unsigned long)dev_cmd,
				0, 0, 0, 0);
	} else {
		rc = (int)app_resume(app_data);
	}

	if (app_data->exit_flag == APP_EXIT_SVC_YIELD_FLAG) {
		rc = DEV_ASSIGN_STATUS_COMM_BLOCKED;
	}

	shared_ret = app_data->el2_shared_page;

	*comm_exit_args = shared_ret->rmi_dev_comm_exit;

	if (shared_ret->cached_digest.len != 0U) {
		if (comm_digest_ptr == NULL) {
			app_unmap_shared_page(app_data);
			return DEV_ASSIGN_STATUS_ERROR;
		}
		(void)memcpy(comm_digest_ptr->value, shared_ret->cached_digest.value,
			     shared_ret->cached_digest.len);
		comm_digest_ptr->len = shared_ret->cached_digest.len;
	}

	app_unmap_shared_page(app_data);

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
	(void)memcpy(app_data->el2_shared_page, (void *)pubkey_params,
		     sizeof(*pubkey_params));
	rc = (int)app_run(app_data, DEVICE_ASSIGN_APP_FUNC_SET_PUBLIC_KEY,
				pubkey_params->algo, 0, 0, 0);
	app_unmap_shared_page(app_data);
	return rc;
}

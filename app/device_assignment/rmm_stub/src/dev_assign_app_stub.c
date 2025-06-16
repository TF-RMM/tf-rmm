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
			int dev_cmd)
{
	int rc;
	struct rmi_dev_comm_enter *shared;
	struct rmi_dev_comm_exit *shared_ret;

	assert((dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_RESUME) ||
		(dev_cmd == DEVICE_ASSIGN_APP_FUNC_ID_CONNECT_INIT));

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
	*comm_exit_args = *shared_ret;
	app_unmap_shared_page(app_data);

	return rc;
}

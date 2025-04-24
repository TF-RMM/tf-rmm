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

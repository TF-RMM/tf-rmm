/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef APP_H
#define APP_H

#include <app_fw_structures.h>

#define APP_VA_START	(UL(0xffffffffffffffff) - XLAT_HIGH_VA_SIZE + 1U)

#ifndef __ASSEMBLER__
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define GRANULE_COUNT(size)	(round_up(size, GRANULE_SIZE) / GRANULE_SIZE)

/*
 * Function to set up the App framework. Called once, during cold boot.
 */
void app_framework_setup(void);

/*
 * Function to calculate the number of per instance granules that are used by
 * this app.
 *
 * Arguments:
 *	- app_id: The ID of the application.
 *
 * Return:
 *	- The number of granules required by the app.
 */
size_t app_get_required_granule_count(unsigned long app_id);

/*
 * Initialise the config data for an App instance.
 *
 * Arguments:
 *	- app_data: Pointer to the config to be initialised
 *	- app_id: The id of the app to be initialised
 *	- granule_pas: An array of Granule PAS that can be used for per instance
 *        data in the app
 *	- granule_count: The number of elements in the granule_pas array.
 *
 * Return:
 *	- 0 on success or a negative POSIX error otherwise.
 */
int app_init_data(struct app_data_cfg *app_data,
		      unsigned long app_id,
		      uintptr_t granule_pas[],
		      size_t granule_count);

/*
 * Resume the app instance execution specified by the app data config. This
 * function loads the app register context, runs the app, and returns to the
 * caller if the app finished running by calling an SVC or caused an exception.
 *
 * Arguments:
 *	- app_data: An initialised app config (selects the app instance to run)
 *	- app_func_id: The id of the function in the app to be run
 *	- arg0 - arg3: Arguments to the app function
 *
 * Return:
 *	- App specific return value
 */
unsigned long app_run(struct app_data_cfg *app_data,
			  unsigned long app_func_id,
			  unsigned long arg0,
			  unsigned long arg1,
			  unsigned long arg2,
			  unsigned long arg3);

/*
 * Map the app shared page in the EL2 VA space
 *
 * Arguments:
 *	- app_data: An initialised app config
 */
void app_map_shared_page(struct app_data_cfg *app_data);

/*
 * Unmap the app shared page from the EL2 VA space
 *
 * Arguments:
 *	- app_data: An initialised app config
 */
void app_unmap_shared_page(struct app_data_cfg *app_data);

#endif /* __ASSEMBLER__ */
#endif /* APP_H */

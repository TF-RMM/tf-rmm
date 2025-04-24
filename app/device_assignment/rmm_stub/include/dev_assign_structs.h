/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef DEV_ASSIGN_STRUCTS_H
#define DEV_ASSIGN_STRUCTS_H

#include <smc-rmi.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define DEV_ASSIGN_STATUS_SUCCESS	(0)
#define DEV_ASSIGN_STATUS_ERROR		(-1)
#define DEV_ASSIGN_STATUS_COMM_BLOCKED	(1)

/*
 * App function for initialization. This needs to be invoked for every
 * new instance of the app. App uses heap available via tpidrro_el0.
 *
 * arg0 == Size of Heap in num of 4K pages.
 *
 * Shared app buf == `struct dev_assign_params`
 *
 * ret0 == DEV_ASSIGN_STATUS_SUCCESS if initialization is successful.
 *         DEV_ASSIGN_STATUS_ERROR if error on initialization.
 */
#define DEVICE_ASSIGN_APP_FUNC_ID_INIT			1

struct dev_assign_params {
	/* RMI device handle */
	void *dev_handle;
	/* Algorithm used to generate device digests. */
	uint8_t rmi_hash_algo;
	/* SPDM certificate slot ID */
	uint8_t cert_slot_id;
	bool has_ide;
	/* Identify the root complex (RC). */
	uint64_t ecam_addr;
	/* Identify the RP within the RC. RootPort PCI BDF */
	uint16_t rp_id;
	/* IDE stream ID */
	uint64_t ide_sid;
};

/* Shared structure on the app heap for SPDM comms */
struct dev_assign_spdm_shared {
	uint8_t sendrecv_buf[GRANULE_SIZE];
};

/*
 * App functions for device communication. App uses heap available via tpidrro_el0.
 * The function execution can yield and return back to RMM. In this case
 * the return would be via APP_YIELD_CALL svc. Callers need to check
 * `app_data->exit_flag` for APP_EXIT_SVC_YIELD_FLAG. The `rmi_dev_comm_enter`
 * is expected to be populated in shared buf for entry into app and
 * `rmm_dev_comm_exit` is expected to be populated for exit from app.
 * These entry and exit data is expected to be populated in the yield case
 * as well.
 *
 * Shared app buf == `struct dev_assign_comm_params`
 *
 * ret0 == DEV_ASSIGN_STATUS_SUCCESS if connection is successful.
 *         DEV_ASSIGN_STATUS_ERROR if error on connection.
 *         NA if app is yielded.
 *
 */
#define DEVICE_ASSIGN_APP_FUNC_ID_CONNECT_INIT		2

/*
 * Pseudo App function ID for device communication resume. App uses heap available via
 * tpidrro_el0. The cmd should only be issued to dev_assign_dev_communicate() if the
 * app was yeilded. The `rmi_dev_comm_enter` is expected to be populated in shared
 * buf for entry into app and `rmm_dev_comm_exit` is expected to be populated for
 * exit from app. The app can yeild again and callers need to check `app_data->exit_flag`
 * for APP_EXIT_SVC_YIELD_FLAG.
 *
 * Note that this function ID is not passed to the app but used in stub to handle
 * resume after a yield (and hence pseudo).
 *
 * Shared app buf == `struct dev_assign_comm_params`
 *
 * ret0 == DEV_ASSIGN_STATUS_SUCCESS if connection is successful.
 *         DEV_ASSIGN_STATUS_ERROR if error on connection.
 *         NA if app is yielded.
 */
#define DEVICE_ASSIGN_APP_FUNC_ID_RESUME		10

/*
 * App function ID to de-initialise. App uses heap available via
 * tpidrro_el0.
 *
 * ret0 == DEV_ASSIGN_STATUS_SUCCESS
 */
#define DEVICE_ASSIGN_APP_FUNC_ID_DEINIT		4

#endif /* DEV_ASSIGN_STRUCTS_H */

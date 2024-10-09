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
 * App function ID to de-initialise. App uses heap available via
 * tpidrro_el0.
 *
 * ret0 == DEV_ASSIGN_STATUS_SUCCESS
 */
#define DEVICE_ASSIGN_APP_FUNC_ID_DEINIT		4

#endif /* DEV_ASSIGN_STRUCTS_H */

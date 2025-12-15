/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef DEV_ASSIGN_STRUCTS_H
#define DEV_ASSIGN_STRUCTS_H

#include <smc-rmi.h>
#include <smc-rsi.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <utils_def.h>

#define DEV_ASSIGN_STATUS_SUCCESS	(0)
#define DEV_ASSIGN_STATUS_ERROR		(-1)
#define DEV_ASSIGN_STATUS_COMM_BLOCKED	(1)

#ifndef CBMC
#define DEV_OBJ_DIGEST_MAX		U(64)
#else
#define DEV_OBJ_DIGEST_MAX		U(4)
#endif /* CBMC */

#define RDEV_START_INTERFACE_NONCE_SIZE		64U

#define CACHE_TYPE_VCA			((uint8_t)0x1)
#define CACHE_TYPE_CERT			((uint8_t)0x2)
#define CACHE_TYPE_MEAS			((uint8_t)0x3)
#define CACHE_TYPE_INTERFACE_REPORT	((uint8_t)0x4)
#define CACHE_TYPE_NONE			((uint8_t)0xFF)

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

enum dev_assign_op_params_type {
	DEV_ASSIGN_OP_PARAMS_NONE,
	DEV_ASSIGN_OP_PARAMS_TDISP,
	DEV_ASSIGN_OP_PARAMS_MEAS
};

/*
 * RMM maintains digest of device object if its cached by NS host. This device
 * object could be VCA, device certificate or device measurement or device
 * interface report
 */
struct dev_obj_digest {
	uint8_t value[DEV_OBJ_DIGEST_MAX];
	size_t len;
};

/* cppcheck-suppress misra-c2012-2.4 */
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
/* cppcheck-suppress misra-c2012-2.4 */
struct dev_assign_spdm_shared {
	uint8_t sendrecv_buf[GRANULE_SIZE];
};

struct dev_assign_tdisp_params {
	uint32_t tdi_id;
	uint8_t start_interface_nonce_buffer[RDEV_START_INTERFACE_NONCE_SIZE];
	bool nonce_ptr_is_valid;
	bool nonce_is_output;
};

/*
 * Get measurements operation related parameters passed when command is
 * RDEV_GET_MEASUREMENTS
 */
/* cppcheck-suppress misra-c2012-2.4 */
struct dev_meas_params {
	/* Get all measurements */
	bool all;

	/* Get signed measurement */
	bool sign;

	/* Get measurement in a raw bitstream */
	bool raw;

	/* Bitmap of measurement indices to get when 'all=false' */
	unsigned char indices[VDEV_MEAS_PARAM_INDICES_LEN];

	/* nonce value used in get measurement, when 'sign=true' */
	unsigned char nonce[VDEV_MEAS_PARAM_NONCE_LEN];
};

struct dev_assign_op_params {
	enum dev_assign_op_params_type param_type;
	union {
		struct dev_meas_params meas_params;
		struct dev_assign_tdisp_params tdisp_params;
	};
};

/*
 * The structure that dev_assign_dev_communicate can use to send data to app
 * shared memory app call
 */
struct dev_comm_enter_shared {
	struct rmi_dev_comm_enter rmi_dev_comm_enter;

	struct dev_assign_op_params dev_assign_op_params;
};
COMPILER_ASSERT(sizeof(struct dev_comm_enter_shared) <= GRANULE_SIZE);

/*
 * The structure that dev_assign_dev_communicate can use to get data from app
 * shared memory on return
 */
struct dev_comm_exit_shared {
	struct rmi_dev_comm_exit rmi_dev_comm_exit;

	struct dev_obj_digest cached_digest;
	/* Type of the cached object (CACHE_TYPE_* defined above) */
	uint32_t cached_digest_type;

	struct dev_assign_op_params dev_assign_op_params;
};
COMPILER_ASSERT(sizeof(struct dev_comm_exit_shared) <= GRANULE_SIZE);

/* cppcheck-suppress misra-c2012-2.4 */
struct dev_tdisp_params {
	/* Interface ID to lock/start/stop/get_report */
	uint32_t tdi_id;

	/*
	 * If the command is lock interface, start_interface_nonce is an output
	 * value.
	 *
	 * If the command is start interface, start_interface_nonce is an input.
	 */
	uint8_t *start_interface_nonce;
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
 * App function to store a public key in the app's keystore.
 *
 * Shared app buf == `struct rmi_public_key_params`
 *
 * ret0 == DEV_ASSIGN_STATUS_SUCCESS if the public key is successfully set.
 *         DEV_ASSIGN_STATUS_ERROR if error occurred during key loading.
 */
#define DEVICE_ASSIGN_APP_FUNC_SET_PUBLIC_KEY		3

/*
 * App function ID to de-initialise. App uses heap available via
 * tpidrro_el0.
 *
 * ret0 == DEV_ASSIGN_STATUS_SUCCESS
 */
#define DEVICE_ASSIGN_APP_FUNC_ID_DEINIT		4

/*
 * App function ID to start a libspdm session
 *
 * ret0 == DEV_ASSIGN_STATUS_SUCCESS if the session is started successfully.
 *         DEV_ASSIGN_STATUS_ERROR if libspdm returned error.
 */
#define DEVICE_ASSIGN_APP_FUNC_ID_SECURE_SESSION	11

/*
 * App function ID to get measurements from the device
 *
 * ret0 == DEV_ASSIGN_STATUS_SUCCESS if the mesurements were retrieved
 *         successfully.
 *         DEV_ASSIGN_STATUS_ERROR if libspdm returned error.
 */
#define DEVICE_ASSIGN_APP_FUNC_ID_GET_MEASUREMENTS	12

/*
 * App function ID to stop the libspdm session that is associated with this app
 * instance.
 *
 * ret0 == DEV_ASSIGN_STATUS_SUCCESS if the session is stopped successfully.
 *         DEV_ASSIGN_STATUS_ERROR if libspdm returned error.
 */
#define DEVICE_ASSIGN_APP_FUNC_ID_STOP_CONNECTION	0x80

/*
 * App function ID to send a LOCK_INTERFACE_REQUEST to a device.
 *
 * Shared app buf == `struct dev_comm_enter_shared`
 *
 * ret0 == DEV_ASSIGN_STATUS_SUCCESS if the device is locked successfully.
 *         DEV_ASSIGN_STATUS_ERROR if locking the device failed.
 */
#define DEVICE_ASSIGN_APP_FUNC_ID_VDM_TDISP_LOCK	0x100

/*
 * App function ID to get Device Interface Report from a device.
 *
 * Shared app buf == `struct dev_comm_enter_shared`
 *
 * ret0 == DEV_ASSIGN_STATUS_SUCCESS if report received successfully.
 *         DEV_ASSIGN_STATUS_ERROR if getting the report failed.
 */
#define DEVICE_ASSIGN_APP_FUNC_ID_VDM_TDISP_REPORT	0x101

/*
 * App function ID to send START_INTERFACE_REQUEST to the device.
 *
 * Shared app buf == `struct dev_comm_enter_shared`
 *
 * ret0 == DEV_ASSIGN_STATUS_SUCCESS if the device interface successfully
 *         transitioned to the run state.
 *         DEV_ASSIGN_STATUS_ERROR if moving the device interface to run
 *         state failed.
 */
#define DEVICE_ASSIGN_APP_FUNC_ID_VDM_TDISP_START	0x102

/*
 * App function ID to send STOP_INTERFACE_REQUEST to the device.
 *
 * Shared app buf == `struct dev_comm_enter_shared`
 *
 * ret0 == DEV_ASSIGN_STATUS_SUCCESS if the device interface transitioned to
 *         unlocked state successfully.
 *         DEV_ASSIGN_STATUS_ERROR if moving the device interface to unlocked
 *         state failed.
 */
#define DEVICE_ASSIGN_APP_FUNC_ID_VDM_TDISP_STOP	0x103

#define DEVICE_ASSIGN_APP_FUNC_ID_IDE_REFRESH		0x200

#define DEVICE_ASSIGN_APP_FUNC_ID_IDE_RESET		0x201

#endif /* DEV_ASSIGN_STRUCTS_H */

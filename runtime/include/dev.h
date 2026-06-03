/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef DEV_H
#define DEV_H

#include <app_fw_structures.h>
#include <arch.h>
#include <arch_features.h>
#include <dev_assign_layout.h>
#include <dev_assign_structs.h>
#include <granule.h>
#include <sizes.h>
#include <smc-rmi.h>
#include <utils_def.h>

/*
 * Represents the state of communication between an RMM device object and a
 * device. The device object could be PDEV or VDEV.
 */
#define DEV_COMM_ACTIVE			U(0)
#define DEV_COMM_ERROR			U(1)
#define DEV_COMM_IDLE			U(2)
#define DEV_COMM_PENDING		U(3)

/* Represents operation being performed by a VDEV. RmmVdevOperation */
#define VDEV_OP_GET_MEAS			U(0)
#define VDEV_OP_GET_REPORT			U(1)
#define VDEV_OP_KEY_PURGE			U(2)
#define VDEV_OP_KEY_REFRESH			U(3)
#define VDEV_OP_LOCK				U(4)
#define VDEV_OP_NONE				U(5)
#define VDEV_OP_START				U(6)
#define VDEV_OP_UNLOCK				U(7)

/* Represents operation performed on a PDEV. RmmPdevOperation */
#define PDEV_OP_CONNECT				U(0)
#define PDEV_OP_DISCONNECT			U(1)
#define PDEV_OP_KEY_PURGE			U(2)
#define PDEV_OP_KEY_REFRESH			U(3)
#define PDEV_OP_NONE				U(4)
#define PDEV_OP_STOP				U(5)
#define PDEV_OP_STREAM_COMPLETE			U(6)

/* Represents the state of a PDEV stream. RmmPdevStreamState */
#define PDEV_STREAM_CONNECTED			U(0)
#define PDEV_STREAM_CONNECTING			U(1)
#define PDEV_STREAM_DISCONNECTED		U(2)
#define PDEV_STREAM_DISCONNECTING		U(3)
#define PDEV_STREAM_KEY_PURGING			U(4)
#define PDEV_STREAM_KEY_REFRESHING		U(5)

/* The following macros return RmiPdevCategory */
#define PDEV_CATEGORY_FROM_FLAGS(flags)		(EXTRACT(RMI_PDEV_FLAGS_CATEGORY, flags))
#define PDEV_CATEGORY(pd_ptr)			(PDEV_CATEGORY_FROM_FLAGS((pd_ptr)->rmi_flags))

enum stream_op_state {
	STREAM_OP_STATE_NONE,
	STREAM_OP_STATE_START,
	STREAM_OP_STATE_RP_READY,
	STREAM_OP_STATE_EP_READY,
	STREAM_OP_STATE_RP_CONNECTED
};

/* A PDEV Stream object. */
struct pdev_stream {
	unsigned long pd1_addr;
	unsigned long pd2_addr;
	unsigned long state; /* RmmPdevStreamState */
	enum stream_op_state op_state;
	unsigned long ide_sid;
	unsigned long num_addr_range;
	struct rmi_address_range addr_range[RMI_PDEV_STREAM_ADDR_RANGE_CNT];
	bool taken;
};

/* PCIe device specific details */
struct pcie_dev {
	/* Device identifier */
	uint64_t bdf;

	/* PCIe Segment identifier of the Root Port and endpoint. */
	uint16_t segment_id;

	/* ECAM base address of the PCIe configuration space */
	uint64_t ecam_addr;

	/* Certificate slot identifier */
	uint64_t cert_slot_id;

	/*
	 * Base and top of requester ID range (inclusive). The value is in
	 * PCI BDF format.
	 */
	unsigned int rid_base;
	unsigned int rid_top;
};

#define PDEV_MAX_VDEVS(vdevs_order)	((1UL << (vdevs_order)) - 1U)
#define PDEV_VDEV_SLOT_INVALID		((unsigned int)-1)

struct pdev_vdev_range_slot {
	bool active;
	unsigned long num_addr_range;
	struct rmi_address_range addr_range[RMI_VDEV_PARAMS_ADDR_RANGE_MAX];
};

struct pdev_op {
	/*
	 * Device interface operation that is in progress. RmmPdevOperation
	 * possible values are PDEV_OP_*
	 */
	unsigned long curr;
	/*
	 * if there is an operation in progress (i.e. op != PDEV_OP_NONE), the
	 * type of the stream that the operation is happening on.
	 */
	unsigned char op_stream_type;

	/* state of the current stream op during pdev communicate */
	enum stream_op_state stream_op_state;
};

#define VDEV_RANGE_SLOTS_PER_GRANULE	(GRANULE_SIZE / sizeof(struct pdev_vdev_range_slot))
/* Round up slot_count to full granules, then divide by slots per granule. */
#define PDEV_VDEV_RANGE_AUX_COUNT_FROM_SLOT_COUNT(slot_count) \
	(((slot_count) + VDEV_RANGE_SLOTS_PER_GRANULE - 1U) / \
	 VDEV_RANGE_SLOTS_PER_GRANULE)
#define PDEV_VDEV_RANGE_AUX_COUNT_FROM_ORDER(vdevs_order) \
	PDEV_VDEV_RANGE_AUX_COUNT_FROM_SLOT_COUNT(PDEV_MAX_VDEVS(vdevs_order))

/*
 * PDEV aux granules:
 * idx 0: The granule containing the stream objects associated with this ep_pdev
 * idx 1..N: pages storing cached VDEV address ranges, where N depends on the
 * requested max_vdevs_order
 * idx after the range pages: app aux pages
 */
#define PDEV_STREAM_AUX_GRANULE_IDX		0U
#define MAX_PDEV_STREAM_AUX_COUNT		1U
#define PDEV_VDEV_RANGES_AUX_GRANULE_IDX					\
		(PDEV_STREAM_AUX_GRANULE_IDX + MAX_PDEV_STREAM_AUX_COUNT)
#define MAX_VDEV_RANGES_AUX_COUNT						\
	PDEV_VDEV_RANGE_AUX_COUNT_FROM_ORDER(MAX_VDEVS_ORDER)
COMPILER_ASSERT(MAX_PDEV_APP_AUX_GRANULES ==
	(MAX_PDEV_PARAM_AUX_GRANULES -
	 (PDEV_VDEV_RANGES_AUX_GRANULE_IDX + MAX_VDEV_RANGES_AUX_COUNT)));

/*
 * PDEV object. Represents a communication channel between the RMM and a
 * physical device, for example a PCIe device.
 */
/* NOLINTNEXTLINE(clang-analyzer-optin.performance.Padding) as fields are in logical order */
struct pdev {
	/* Pointer to this granule */
	struct granule *g_pdev;

	/* State of this PDEV. RmmPdevState */
	unsigned long rmi_state;

	/* Flags provided by the Host during PDEV creation. RmiPdevFlags */
	unsigned long rmi_flags;

	/* Number of VDEVs associated with this PDEV */
	uint32_t num_vdevs;
	uint32_t max_num_vdevs;

	/* Number and addresses of PDEV app auxiliary granules */
	struct granule *g_app_aux[MAX_PDEV_APP_AUX_GRANULES];
	unsigned int num_app_aux;

	/* The aux granules holding the VDEV ranges associated with this PDEV */
	struct granule *g_vdevs_ranges_aux[MAX_VDEV_RANGES_AUX_COUNT];

	/*
	 * Algorithm used to generate device digests. This value is returned to
	 * Realm as part of RDEV_GET_INFO call
	 */
	uint8_t rmi_hash_algo;

	/* Digest of VCA (Version, Capabilities, Algorithm)*/
	struct dev_obj_digest vca_digest;

	/*
	 * Digest of device certificate. This digest is calculated when RMM
	 * fetches device certificate. The content of the certificate is cached
	 * by NS host.
	 */
	struct dev_obj_digest cert_digest;

	/* Device communication state. RmmDevCommState */
	unsigned int dev_comm_state;

	struct pdev_op op;

	/*
	 * The number of streams that are associated with this pdev. (i.e.
	 * there is a stream operation in progress on this pdev or there is a
	 * stream in state PDEV_STREAM_CONNECTED where one of the pdevs is this
	 * object). This can be used to prevent pdev_destroy while a stream
	 * is associated with this pdev.
	 */
	unsigned long associated_stream_count;
	/*
	 * The granule containing the streams of the endpoint participating in
	 * this stream. Set when op changes from PDEV_OP_NONE to something else.
	 */
	struct granule *g_stream_aux;

	/* The associated device */
	struct pcie_dev dev;

	/* DA app cfg */
	struct app_data_cfg da_app_data;
	bool da_app_yielded;
};
COMPILER_ASSERT(sizeof(struct pdev) <= GRANULE_SIZE);

struct vdev_attest_info {
	unsigned long lock_nonce;
	unsigned long meas_nonce;
	unsigned long report_nonce;
};

/*
 * VDEV object. Represents the binding between a device function and a Realm. For
 * example, a VDEV can represent a physical function of a PCIe device or a
 * virtual function of a multi-function PCIe device. Every VDEV is associated
 * with one PDEV.
 */
struct vdev {

	/* The Realm to which this device is assigned */
	struct granule *g_rd;

	/* The PDEV to which this VDEV belongs */
	struct granule *g_pdev;

	/*
	 * For a PCIe device this is the routing identifier of the virtual
	 * endpoint.
	 */
	uint64_t id;

	/* TDI identifier */
	uint64_t tdi_id;

	/* State of this VDEV. RmmVdevState */
	uint32_t rmi_state;

	/* State of the VDEV communication. RmmDevCommState */
	uint32_t comm_state;

	/* DMA state */
	uint32_t dma_state;

	/* StreamId */
	uint32_t sid;

	/* SMMU index */
	uint32_t smmu_idx;

	/*
	 * Digest of device measurements and interface report. This digest is
	 * calculated when RMM fetches these objects. The content of these device
	 * objects are cached by NS host.
	 */
	struct dev_obj_digest meas_digest;
	struct dev_obj_digest ifc_report_digest;

	struct vdev_attest_info attest_info;

	/*
	 * Device interface operation that is in progress. RmmVdevOperation
	 * possible values are VDEV_OP_*
	 */
	unsigned long op;

	/*
	 * The parameters passed from Realm for the device operation. There can
	 * be only one pending device operation.
	 */
	union {
		/*
		 * RMI_VDEV_GET_MEASUREMENTS(rd, call sets this meas_params. 'op'
		 * must be VDEV_OP_GET_MEAS
		 */
		struct dev_meas_params meas_params;

		/*
		 * RMI_VDEV_{LOCK/START/GET_INTERFACE_REPORT} call set this
		 * parameter
		 */
		struct dev_tdisp_params tdisp_params;
	} op_params;

	/* Nonce updated as part of lock interface and used in start interface */
	uint8_t start_interface_nonce[RDEV_START_INTERFACE_NONCE_SIZE];

	/* Device address ranges */
	unsigned long num_addr_range;
	struct rmi_address_range addr_range[RMI_VDEV_PARAMS_ADDR_RANGE_MAX];
	uint32_t pdev_slot;

};
COMPILER_ASSERT(sizeof(struct vdev) <= GRANULE_SIZE);

unsigned long dev_communicate(struct pdev *pd, struct vdev *vd,
			      struct granule *g_dev_comm_data);
struct pdev_stream *pdev_stream_granules_lock_map(struct granule *g_streams,
						  unsigned char stream_type);
void pdev_stream_granules_unmap_unlock(struct granule *g_streams,
				       struct pdev_stream *stream,
				       unsigned char stream_type);
void pdev_continue_handler(unsigned long fid, struct smc_result *res);
#endif /* DEV_H */

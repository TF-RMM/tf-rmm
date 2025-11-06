/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef DEV_H
#define DEV_H

#include <app_fw_structures.h>
#include <arch.h>
#include <arch_features.h>
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
#define VDEV_OP_LOCK				U(2)
#define VDEV_OP_NONE				U(3)
#define VDEV_OP_P2P_BIND			U(4)
#define VDEV_OP_P2P_UNBIND			U(5)
#define VDEV_OP_START				U(6)
#define VDEV_OP_UNLOCK				U(7)

/* PCIe device specific details */
struct pcie_dev {
	/* Device identifier */
	uint64_t bdf;

	/* PCIe Segment identifier of the Root Port and endpoint. */
	uint16_t segment_id;

	/*
	 * Physical PCIe routing identifier of the Root Port to which the
	 * endpoint is connected.
	 */
	uint16_t root_id;

	/* ECAM base address of the PCIe configuration space */
	uint64_t ecam_addr;

	/* Certificate slot identifier */
	uint64_t cert_slot_id;

	/* IDE stream ID */
	uint64_t ide_sid;

	/*
	 * Base and top of requester ID range (inclusive). The value is in
	 * PCI BDF format.
	 */
	uint64_t rid_base;
	uint64_t rid_top;

	/* Device non-coherent address range and its range */
	struct rmi_address_range
			ncoh_addr_range[PDEV_PARAM_NCOH_ADDR_RANGE_MAX];
	uint64_t ncoh_num_addr_range;
};

/*
 * PDEV object. Represents a communication channel between the RMM and a
 * physical device, for example a PCIe device.
 */
struct pdev {
	/* Pointer to this granule */
	struct granule *g_pdev;

	/* State of this PDEV. RmmPdevState */
	unsigned long rmi_state;

	/* Flags provided by the Host during PDEV creation. RmiPdevFlags */
	unsigned long rmi_flags;

	/* Number of VDEVs associated with this PDEV */
	uint32_t num_vdevs;

	/* Number and addresses of PDEV auxiliary granules */
	struct granule *g_aux[PDEV_PARAM_AUX_GRANULES_MAX];
	unsigned int num_aux;

	/*
	 * Algorithm used to generate device digests. This value is returned to
	 * Realm as part of RDEV_GET_INFO call
	 */
	uint8_t rmi_hash_algo;

	/*
	 * Digest of device certificate. This digest is calculated when RMM
	 * fetches device certificate. The content of the certificate is cached
	 * by NS host.
	 */
	struct dev_obj_digest cert_digest;

	/* Device communication state. RmmDevCommState */
	unsigned int dev_comm_state;

	/* The associated device */
	struct pcie_dev dev;

	/* DA app cfg */
	struct app_data_cfg da_app_data;
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

	/*
	 * Number of Granules of this VDEV’s memory which have been mapped into
	 * the owning Realm’s address space
	 */
	uint64_t num_map;

	/* TDI identifier */
	uint64_t tdi_id;

	/* State of this VDEV. RmmVdevState */
	uint32_t rmi_state;

	/* State of the VDEV communication. RmmDevCommState */
	uint32_t comm_state;

	/* DMA state */
	uint32_t dma_state;

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
};
COMPILER_ASSERT(sizeof(struct vdev) <= GRANULE_SIZE);

unsigned long dev_communicate(struct pdev *pd, struct vdev *vd,
			      struct granule *g_dev_comm_data);
#endif /* DEV_H */

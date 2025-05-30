/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef DEV_H
#define DEV_H

#include <app_fw_structures.h>
#include <arch.h>
#include <arch_features.h>
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

	/* State of this PDEV. RmiPdevState */
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

	/* Device communiction state */
	unsigned int dev_comm_state;

	/* The associated device */
	struct pcie_dev dev;

	/* DA app cfg */
	struct app_data_cfg da_app_data;
};
COMPILER_ASSERT(sizeof(struct pdev) <= GRANULE_SIZE);

#endif /* DEV_H */

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_DA_H
#define HOST_DA_H

#include <smc-rmi.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* The Host DA fixture uses a four-level Realm RTT. */
#define RTT_COUNT		4
#define HOST_DA_VDEV_ID		0U

struct host_realm {
	void *rd;
	void *rec;
	void *rtts[RTT_COUNT];
	struct rmi_realm_params *realm_params;
	struct rmi_rec_params *rec_params;
	struct rmi_rec_run *rec_run;
	uintptr_t realm_data_1;
	size_t realm_data_1_num_gr;
	uintptr_t realm_data_2;
	size_t realm_data_2_num_gr;
};

/* Opaque state owned by the Host DA driver. */
struct host_pdev;
struct host_vdev;

/* Each Host variant supplies its own non-overlapping granule allocator. */
void *allocate_granule(unsigned int num_granules);
void *allocate_granule_aligned(unsigned int num_granules);

/* Complete an SRO, including any Host-owned memory donation or reclaim. */
int host_sro_drive(unsigned long handle, unsigned long ret_status,
		   unsigned long donate_req);

/* Set up a PDEV and PSMMU; return a PDEV ID or zero on success, respectively. */
int host_pdev_probe_and_setup(void);
int host_psmmu_setup(unsigned int smmu_idx, unsigned long sid);

/* Assign, run and reclaim DA devices; return IDs or zero on success. */
int host_vdev_assign(struct host_realm *realm, unsigned long host_vdev_tdi_id);
int host_realm_run_da(struct host_realm *realm);
int host_pdev_reclaim(int host_pdev_id);
int host_vdev_reclaim(struct host_realm *realm, int host_vdev_id);

/* Return the Host driver's singleton PDEV and VDEV contexts. */
struct host_pdev *host_pdev_current(void);
struct host_vdev *host_vdev_current(void);

/* Return the RMI object and NS communication page owned by a PDEV context. */
void *host_pdev_ptr(struct host_pdev *pdev, bool endpoint);
struct rmi_dev_comm_data *host_pdev_comm_data(struct host_pdev *pdev);

/* Return the RMI object and NS communication page owned by a VDEV context. */
void *host_vdev_ptr(struct host_vdev *vdev);
struct rmi_dev_comm_data *host_vdev_comm_data(struct host_vdev *vdev);

/* Prepare and create a PDEV; both calls return zero on success. */
int host_pdev_setup(struct host_pdev *pdev);
int host_pdev_create(struct host_pdev *pdev, bool endpoint);

/* Drive PDEV destruction or a stream disconnect; return zero on success. */
int host_pdev_destroy(struct host_pdev *pdev, bool endpoint);
int host_pdev_stream_disconnect(struct host_pdev *pdev);

/* Release Host-side PDEV resources once its RMI object is absent. */
void host_pdev_cleanup(struct host_pdev *pdev, bool endpoint);

/*
 * Drive PDEV/VDEV communication until the requested state and exit condition.
 * A VDEV requires a Realm context; a PDEV uses endpoint to select its object.
 * Return zero on success or -1 on an RMI, transport or state failure.
 */
int host_dev_communicate(struct host_realm *realm, struct host_pdev *pdev,
			 bool endpoint, struct host_vdev *vdev,
			 unsigned char target_state, bool wait_for_stream);

#endif /* HOST_DA_H */

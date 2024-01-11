/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TB_REALM_H
#define TB_REALM_H

#include <measurement.h>
#include <realm.h>
#include <smc-rmi.h>
#include <tb_granules.h>

#define DESTROYED RIPAS_DESTROYED
#define EMPTY RIPAS_EMPTY
#define RAM RIPAS_RAM

extern unsigned long vmids[];

enum rmm_rtt_entry_state {
	ASSIGNED,
	ASSIGNED_NS,
	TABLE,
	UNASSIGNED,
	UNASSIGNED_NS,
};

struct rmm_realm {
	uint64_t ipa_width;
	uint64_t measurements[MEASUREMENT_SLOT_NR];
	uint64_t hash_algo;
	uint64_t rec_index;
	uint64_t rtt_base;
	uint64_t rtt_level_start;
	uint64_t rtt_num_start;
	uint64_t state;
	uint64_t vmid;
	uint8_t rpv[RPV_SIZE];
};

struct rmi_realm_params_buffer {
	uint8_t flags;
	uint8_t s2sz;
	uint8_t sve_vl;
	uint8_t num_bps;
	uint8_t num_wps;
	uint8_t pmu_num_ctrs;
	uint8_t hash_algo;
	uint8_t rpv[RPV_SIZE];
	uint16_t vmid;
	uint64_t rtt_base;
	int64_t rtt_level_start;
	uint32_t rtt_num_start;
};

bool VmidIsFree(uint16_t vmid);
bool RealmIsLive(uint64_t rd_addr);
bool RttsStateEqual(uint64_t base, uint64_t number_start, uint64_t state);
struct rmm_realm Realm(uint64_t rd);

struct rd nondet_struct_rd(void);
struct rmm_realm nondet_struct_rmm_realm(void);

struct granule *init_realm_descriptor_page(void);

uint64_t RecAuxCount(uint64_t rd_addr);

#endif /* TB_REALM_H */


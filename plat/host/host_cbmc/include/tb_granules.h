/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TB_GRANULES_H
#define TB_GRANULES_H

#include "buffer.h"
#include "granule.h"
#include "granule_types.h"
#include "host_defs.h"
#include "host_utils.h"
#include "platform_api.h"
#include "sizes.h"

/*
 * The granule states and gpt state
 */
#define UNDELEGATED GRANULE_STATE_NS
#define DELEGATED GRANULE_STATE_DELEGATED
#define RD GRANULE_STATE_RD
#define DATA GRANULE_STATE_DATA
#define REC GRANULE_STATE_REC
#define RTT GRANULE_STATE_RTT

#define RMM_GRANULE_SIZE GRANULE_SIZE

enum granule_gpt {
	GPT_SECURE,
	GPT_NS,
	GPT_REALM,
	GPT_ROOT,
	GPT_AAP
};

struct SPEC_granule {
	enum granule_gpt gpt;
	unsigned char state;
};

/*
 * CBMC needs access to the below data structures which are not otherwise
 * visible outside their respective files.
 */
extern unsigned char granules_buffer[HOST_MEM_SIZE];
extern struct granule granules[RMM_MAX_GRANULES];

/*
 * Declare nondet_* functions.
 * CBMC automatically returns nondet values based on the return types.
 * However, enum is treated as integer hence the value might out of range.
 */
struct granule nondet_struct_granule(void);
struct SPEC_granule nondet_struct_SPEC_granule(void);

bool valid_granule_ptr(struct granule *p);
struct granule init_granule(void);
void init_granule_and_page(void);

/*
 * Pedicates
 */
bool AddrIsGranuleAligned(uint64_t addr);
bool PaIsDelegable(uint64_t addr);
struct SPEC_granule Granule(uint64_t addr);

#endif /* !TB_GRANULES_H */

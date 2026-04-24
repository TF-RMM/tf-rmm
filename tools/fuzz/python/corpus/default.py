#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

from fuzzer_protocol import *

if __name__ == "__main__":
    packets = []

    packets.append(Features(index=1))

    # Granule index assignments
    rd          = 0
    rec         = 1
    realm_params = 2
    rec_params  = 3
    rec_run     = 4
    # RTT granules: rtt[0] is the start table, rtt[1..6] are sub-tables.
    # We need two sets of 3 sub-tables: one for IPA=0 and one for IPA=2**47.
    rtt_base    = 5   # rtt[0] – passed as rtt_base in realm_params
    # rtt[1,2,3]: sub-tables for protected IPA region (IPA 0)
    # rtt[4,5,6]: sub-tables for unprotected IPA region (IPA 2**47)
    realm_data  = 12
    realm_data2 = 13
    src         = 14
    src2        = 15

    GRANULE_SIZE    = 0x1000
    REALM_DATA_IPA  = 0x1000
    UNPROTECTED_IPA = 2 ** 47   # IPA bit 47 set → NS/unprotected space

    # --- Allocate all granules ---
    for idx in [rd, rec, realm_params, rec_params, rec_run]:
        packets.append(AllocateGranule(index=idx))

    # Allocate 7 RTT granules (rtt[0..6]) and delegate them all
    for i in range(7):
        packets.append(AllocateGranule(index=rtt_base + i))
        packets.append(GranuleDelegate(index=rtt_base + i))

    # Delegate rd and rec
    packets.append(GranuleDelegate(index=rd))
    packets.append(GranuleDelegate(index=rec))

    # Allocate and delegate data granules
    packets.append(AllocateGranule(index=realm_data))
    packets.append(GranuleDelegate(index=realm_data))
    packets.append(AllocateGranule(index=realm_data2))
    packets.append(GranuleDelegate(index=realm_data2))

    # Allocate source granules (NS – used to seed data map)
    packets.append(AllocateGranule(index=src))
    packets.append(AllocateGranule(index=src2))

    # --- Realm create ---
    # s2sz=0x30 (48-bit PA), rtt_level_start=0 means 4-level walk starting
    # from L0; rtt_num_start=1 means one L0 RTT entry (rtt[0]).
    packets.append(
        RealmCreate(rd_index=rd, param_index=realm_params,
                    s2sz=0x30, num_bps=1, num_wps=1,
                    rtt_base_index=rtt_base, rtt_level_start=0, rtt_num_start=1))

    # --- Create RTT sub-tables for protected IPA 0 (levels 1, 2, 3) ---
    for level in range(1, 4):
        packets.append(RTTCreate(rd_index=rd, rtt_index=rtt_base + level,
                                 ipa=0, level=level))

    # --- Create RTT sub-tables for unprotected IPA 2**47 (levels 1, 2, 3) ---
    for level in range(1, 4):
        packets.append(RTTCreate(rd_index=rd, rtt_index=rtt_base + 3 + level,
                                 ipa=UNPROTECTED_IPA, level=level))

    # --- Map data granules into the protected IPA space ---
    packets.append(RTTReadEntry(rd_index=rd, ipa=0, level=1))
    packets.append(RttInitRipas(rd_index=rd,
                                base=REALM_DATA_IPA,
                                top=REALM_DATA_IPA + 2 * GRANULE_SIZE))
    packets.append(RttDataMapInit(rd_index=rd, data_index=realm_data,
                                  ipa=REALM_DATA_IPA, src=src))
    packets.append(RttDataMapInit(rd_index=rd, data_index=realm_data2,
                                  ipa=REALM_DATA_IPA + GRANULE_SIZE, src=src2))

    # --- Create REC then drive SRO protocol to donate aux granules ---
    packets.append(RecCreate(rd_index=rd, rec_index=rec,
                             param_index=rec_params, flags=0x1))
    packets.append(SroDonate(count=0))
    packets.append(SroContinue(flags=0))

    # --- Activate realm ---
    packets.append(RealmActivate(rd_index=rd))

    # --- Map an NS (unprotected) page for the realm to use ---
    packets.append(RTTMapUnprotected(rd_index=rd, ipa=UNPROTECTED_IPA,
                                     level=3, desc=0b1100))

    # --- Enter realm ---
    packets.append(RecEnter(rec_index=rec, run_index=rec_run))

    # --- Teardown ---
    # Unmap unprotected entry
    packets.append(RTTUnmapUnprotected(rd_index=rd, ipa=UNPROTECTED_IPA, level=3))

    # Destroy REC then drive SRO protocol to reclaim aux granules
    packets.append(RecDestroy(rec_index=rec))
    packets.append(SroReclaim(list_entries=255))
    packets.append(SroContinue(flags=0))

    # Unmap and undelegate data granules
    packets.append(RttDataUnmap(rd_index=rd,
                                base=REALM_DATA_IPA,
                                top=REALM_DATA_IPA + GRANULE_SIZE,
                                flags=0x1))
    packets.append(RttDataUnmap(rd_index=rd,
                                base=REALM_DATA_IPA + GRANULE_SIZE,
                                top=REALM_DATA_IPA + 2 * GRANULE_SIZE,
                                flags=0x1))
    packets.append(GranuleUndelegate(index=realm_data))
    packets.append(GranuleUndelegate(index=realm_data2))

    # Destroy RTT sub-tables for IPA 0 (deepest first: 3, 2, 1)
    for level in range(3, 0, -1):
        packets.append(RTTDestroy(rd_index=rd, ipa=0, level=level))
        packets.append(GranuleUndelegate(index=rtt_base + level))

    # Destroy RTT sub-tables for IPA 2**47 (deepest first: 3, 2, 1)
    for level in range(3, 0, -1):
        packets.append(RTTDestroy(rd_index=rd, ipa=UNPROTECTED_IPA, level=level))
        packets.append(GranuleUndelegate(index=rtt_base + 3 + level))

    # Destroy realm and undelegate remaining granules
    packets.append(RealmDestroy(rd_index=rd))
    packets.append(GranuleUndelegate(index=rtt_base))   # rtt[0]
    packets.append(GranuleUndelegate(index=rd))
    packets.append(GranuleUndelegate(index=rec))

    import os
    import sys

    os.makedirs(os.path.dirname(sys.argv[1]), exist_ok=True)
    with open(sys.argv[1], "wb") as f:
        for p in packets:
            rmi_packet = RMI() / p
            f.write(raw(rmi_packet))


    # void *rd = allocate_granule();
    rd = 0
    packets.append(AllocateGranule(index=rd))

    # void *rec = allocate_granule();
    rec = 1
    packets.append(AllocateGranule(index=rec))

    # struct rmi_realm_params *realm_params = allocate_granule();
    # struct rmi_rec_params *rec_params = allocate_granule();
    # struct rmi_rec_run *rec_run = allocate_granule();
    realm_params = 2
    rec_params = 3
    rec_run = 4
    packets.append(AllocateGranule(index=realm_params))
    packets.append(AllocateGranule(index=rec_params))
    packets.append(AllocateGranule(index=rec_run))

    # host_rmi_granule_delegate(rd, &result);
    # CHECK_RMI_RESULT();
    # host_rmi_granule_delegate(rec, &result);
    # CHECK_RMI_RESULT();
    packets.append(GranuleDelegate(index=rd))
    packets.append(GranuleDelegate(index=rec))

    # for (i = 0; i < RTT_COUNT; ++i) {
    #	rtts[i] = allocate_granule();
    #	host_rmi_granule_delegate(rtts[i], &result);
    #	CHECK_RMI_RESULT();
    # }
    rtt_base = 5
    for i in range(7):
        packets.append(AllocateGranule(index=rtt_base + i))
        packets.append(GranuleDelegate(index=rtt_base + i))

    # memset(realm_params, 0, sizeof(*realm_params));
    # realm_params->s2sz = arch_feat_get_pa_width();
    # realm_params->rtt_num_start = 1;
    # realm_params->rtt_base = (uintptr_t)rtts[0];
    # host_rmi_realm_create(rd, realm_params, &result);
    # CHECK_RMI_RESULT();
    packets.append(
        RealmCreate(rd_index=rd, param_index=realm_params,
                    s2sz=0x30, num_bps=0x1, num_wps=0x1,
                    rtt_base_index=rtt_base, rtt_num_start=1))
    # /* Create RTT table to start at IPA 0x0 */
    # for (i = 1; i < RTT_COUNT; ++i) {
    #	host_rmi_rtt_create(rd, rtts[i], 0, i, &result);
    #	CHECK_RMI_RESULT();
    # }
    for i in range(1, 4):
        packets.append(RTTCreate(rd_index=rd, rtt_index=rtt_base + i, ipa=(2 ** 47), level=i))

    for i in range(4, 7):
        packets.append(RTTCreate(rd_index=rd, rtt_index=rtt_base + i, ipa=0, level=i - 3))

    # realm_buffer = (uintptr_t)allocate_granule();
    # host_rmi_granule_delegate((void *)realm_buffer, &result);
    # CHECK_RMI_RESULT();
    realm_buffer = 12
    packets.append(AllocateGranule(index=realm_buffer))
    packets.append(GranuleDelegate(index=realm_buffer))

    realm_buffer2 = 13
    packets.append(AllocateGranule(index=realm_buffer2))
    packets.append(GranuleDelegate(index=realm_buffer2))

    src = 14
    packets.append(AllocateGranule(index=src))

    src2 = 15
    packets.append(AllocateGranule(index=src2))

    REALM_BUFFER_IPA = 0x1000
    GRANULE_SIZE = 0x1000
    packets.append(RTTReadEntry(rd_index=rd, ipa=0, level=1))
    packets.append(RttInitRipas(rd_index=rd, base=REALM_BUFFER_IPA,
                                top=REALM_BUFFER_IPA + 2 * GRANULE_SIZE))

    packets.append(RttDataMapInit(rd_index=rd, data_index=realm_buffer,
                                  ipa=REALM_BUFFER_IPA, src=src))
    packets.append(RttDataMapInit(rd_index=rd, data_index=realm_buffer2,
                                  ipa=REALM_BUFFER_IPA + GRANULE_SIZE, src=src2))

    # Aux granules donated via explicit SRO protocol

    # rec_params->flags |= REC_PARAMS_FLAG_RUNNABLE;
    # rec_params->pc = (uintptr_t)realm_start;
    # host_rmi_rec_create(rd, rec, rec_params, &result);
    # CHECK_RMI_RESULT();
    packets.append(RecCreate(
        rd_index=rd,
        rec_index=rec,
        param_index=rec_params,
        flags=0x1,
    ))
    packets.append(SroDonate(count=0))
    packets.append(SroContinue(flags=0))

    # host_rmi_realm_activate(rd, &result);
    # CHECK_RMI_RESULT();
    packets.append(RealmActivate(rd_index=rd))

    packets.append(RTTMapUnprotected(rd_index=rd, ipa=(2 ** 47), level=3, desc=0b1100))

    # /* Execute the Realm */
    # memset(rec_run, 0, sizeof(*rec_run));
    # host_rmi_rec_enter(rec, rec_run, &result);
    # CHECK_RMI_RESULT();
    packets.append(RecEnter(rec_index=rec, run_index=rec_run))

    # while (rec_run->exit.exit_reason == RMI_EXIT_IRQ) {
    #	/* Clear the IRQ in ISR_EL1 and re-enter Realm */
    #	host_write_sysreg("isr_el1", 0x0);
    #	host_rmi_rec_enter(rec, rec_run, &result);
    #	CHECK_RMI_RESULT();
    # }

    # if (rec_run->exit.exit_reason == RMI_EXIT_FIQ) {
    #	INFO("Realm executed successfully and exited due to FIQ.\n");
    # }

    # host_rmi_rec_destroy(rec, &result);
    # CHECK_RMI_RESULT();
    packets.append(RTTUnmapUnprotected(rd_index=rd, ipa=2 ** 47, level=3))
    # Reclaim aux granules via explicit SRO protocol
    packets.append(RecDestroy(rec_index=rec))
    packets.append(SroReclaim(list_entries=255))
    packets.append(SroContinue(flags=0))

    # host_rmi_data_destroy(rd, REALM_BUFFER_IPA, &result);
    # CHECK_RMI_RESULT();
    # host_rmi_granule_undelegate((void *)realm_buffer, &result);
    # CHECK_RMI_RESULT();
    packets.append(RttDataUnmap(rd_index=rd, base=REALM_BUFFER_IPA,
                                top=REALM_BUFFER_IPA + GRANULE_SIZE, flags=0x1))
    packets.append(RttDataUnmap(rd_index=rd, base=REALM_BUFFER_IPA + GRANULE_SIZE,
                                top=REALM_BUFFER_IPA + 2 * GRANULE_SIZE, flags=0x1))
    packets.append(GranuleUndelegate(index=realm_buffer))

    # for (i = RTT_COUNT-1; i >= 1; --i) {
    #	host_rmi_rtt_destroy(rd, 0, i, &result);
    #	CHECK_RMI_RESULT();
    #	host_rmi_granule_undelegate(rtts[i], &result);
    #	CHECK_RMI_RESULT();
    # }
    for i in range(6, 3, -1):
        packets.append(RTTDestroy(rd_index=rd, ipa=0, level=i - 3))
        packets.append(GranuleUndelegate(index=rtt_base + i))
    for i in range(3, 0, -1):
        packets.append(RTTDestroy(rd_index=rd, ipa=2 ** 47, level=i))
        packets.append(GranuleUndelegate(index=rtt_base + i))
    # host_rmi_realm_destroy(rd, &result);
    # CHECK_RMI_RESULT();
    # host_rmi_granule_undelegate(rd, &result);
    # CHECK_RMI_RESULT();
    # host_rmi_granule_undelegate(rec, &result);
    # CHECK_RMI_RESULT();
    packets.append(RealmDestroy(rd_index=rd))
    packets.append(GranuleUndelegate(index=rtt_base))
    packets.append(GranuleUndelegate(index=rd))
    packets.append(GranuleUndelegate(index=rec))

    import os
    import sys

    os.makedirs(os.path.dirname(sys.argv[1]), exist_ok=True)
    with open(sys.argv[1], "wb") as f:
        for p in packets:
            rmi_packet = RMI() / p
            f.write(raw(rmi_packet))

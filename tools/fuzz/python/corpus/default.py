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

    # --- Queue RSI calls to be executed inside the realm ---
    # RSI_VERSION
    packets.append(RsiCall(fid=0xC4000190, arg1=0x00010000))
    # RSI_FEATURES (register 0)
    packets.append(RsiCall(fid=0xC4000191, arg1=0))
    # RSI_REALM_CONFIG (IPA of realm buffer)
    packets.append(RsiCall(fid=0xC4000196, arg1=REALM_DATA_IPA))
    # RSI_MEASUREMENT_READ (index 0)
    packets.append(RsiCall(fid=0xC4000192, arg1=0))
    # RSI_ATTEST_TOKEN_INIT (64-byte challenge split across arg1..arg8)
    packets.append(RsiCall(fid=0xC4000194,
                           arg1=0xDEADBEEF01020304, arg2=0x0506070809101112,
                           arg3=0x1314151617181920, arg4=0x2122232425262728,
                           arg5=0x2930313233343536, arg6=0x3738394041424344,
                           arg7=0x4546474849505152, arg8=0x5354555657585960))
    # RSI_ATTEST_TOKEN_CONTINUE (write token to REALM_DATA_IPA, offset=0, size=256)
    packets.append(RsiCall(fid=0xC4000195,
                           arg1=REALM_DATA_IPA, arg2=0, arg3=0x100))

    # --- Enter realm (drains queued RSI calls) ---
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

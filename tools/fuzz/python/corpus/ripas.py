#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

from fuzzer_protocol import *

if __name__ == "__main__":
    packets = []

    rd = 0
    rec = 1
    realm_params = 2
    rec_params = 99
    rec_run = 4
    rtt_base = 5

    packets.append(AllocateGranule(index=rd))
    packets.append(AllocateGranule(index=rec))
    packets.append(AllocateGranule(index=realm_params))
    packets.append(AllocateGranule(index=rec_params))
    packets.append(AllocateGranule(index=rec_run))

    packets.append(GranuleDelegate(index=rd))
    packets.append(GranuleDelegate(index=rec))

    for i in range(4):
        packets.append(AllocateGranule(index=rtt_base + i))
        packets.append(GranuleDelegate(index=rtt_base + i))

    packets.append(
        RealmCreate(rd_index=rd, param_index=realm_params,
                    s2sz=0x30, num_bps=0x1, num_wps=0x1,
                    rtt_base_index=rtt_base, rtt_num_start=1))

    for i in range(1, 4):
        packets.append(RTTCreate(rd_index=rd, rtt_index=rtt_base + i, ipa=0, level=i))

    REALM_BUFFER_IPA = 0x1000
    GRANULE_SIZE = 0x1000
    # packets.append(RTTReadEntry(rd_index=rd, ipa=0, level=1))
    packets.append(RttInitRipas(rd_index=rd, base=REALM_BUFFER_IPA,
                                top=REALM_BUFFER_IPA + GRANULE_SIZE))

    realm_buffer = 9
    packets.append(AllocateGranule(index=realm_buffer))
    packets.append(GranuleDelegate(index=realm_buffer))

    src = 10
    packets.append(AllocateGranule(index=src))
    packets.append(RttDataMapInit(rd_index=rd, data_index=realm_buffer,
                                  ipa=REALM_BUFFER_IPA, src=src))

    # Aux granules donated via explicit SRO protocol
    packets.append(RecCreate(
        rd_index=rd,
        rec_index=rec,
        param_index=rec_params,
        flags=0x1,
    ))
    packets.append(SroDonate(count=0))
    packets.append(SroContinue(flags=0))

    packets.append(RealmActivate(rd_index=rd))
    packets.append(RecEnter(rec_index=rec, run_index=rec_run))
    packets.append(RttSetRipas(rd_index=rd, rec_index=rec,
                               base=REALM_BUFFER_IPA,
                               top=REALM_BUFFER_IPA + GRANULE_SIZE))

    ### Destroy
    # Aux granules reclaimed via explicit SRO protocol
    packets.append(RecDestroy(rec_index=rec))
    packets.append(SroReclaim(list_entries=255))
    packets.append(SroContinue(flags=0))

    packets.append(RttDataUnmap(rd_index=rd, base=REALM_BUFFER_IPA,
                                top=REALM_BUFFER_IPA + GRANULE_SIZE, flags=0x1))
    packets.append(GranuleUndelegate(index=realm_buffer))

    for i in range(3, 0, -1):
        packets.append(RTTDestroy(rd_index=rd, ipa=0, level=i))
        packets.append(GranuleUndelegate(index=rtt_base + i))

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

#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

from fuzzer_protocol import *

if __name__ == "__main__":
    """PMU flow, enable PMU with flags=0x4 and pmu_num_ctrs=0x1f on Realm Creation

    RmiRealmFlags fieldset:
    0:0  | lpa2 | Whether LPA2 is enabled
    1:1  | sve  | Whether SVE is enabled
    2:2  | pmu  | Whether PMU is enabled
    63:3 | Reserved

    pmu_num_ctrs Requested number of PMU counters
    """
    packets = []

    packets.append(Features(index=26))

    rd = 0
    rec = 1
    realm_params = 2
    rec_params = 3
    rec_run = 4
    rtt_base = 5

    packets.append(AllocateGranule(index=rd))
    packets.append(AllocateGranule(index=rec))
    packets.append(AllocateGranule(index=realm_params))
    packets.append(AllocateGranule(index=rec_params))
    packets.append(AllocateGranule(index=rec_run))
    packets.append(AllocateGranule(index=rtt_base))

    packets.append(GranuleDelegate(index=rd))
    packets.append(GranuleDelegate(index=rec))
    packets.append(GranuleDelegate(index=rtt_base))

    ### Create Realm:
    packets.append(
        RealmCreate(rd_index=rd, param_index=realm_params,
                    flags=0x4, pmu_num_ctrs=0x1f,
                    s2sz=0x30, num_bps=0x1, num_wps=0x1,
                    rtt_base_index=rtt_base, rtt_num_start=1))

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

    ### Destroy:
    # Aux granules reclaimed via explicit SRO protocol
    packets.append(RecDestroy(rec_index=rec))
    packets.append(SroReclaim(list_entries=255))
    packets.append(SroContinue(flags=0))

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

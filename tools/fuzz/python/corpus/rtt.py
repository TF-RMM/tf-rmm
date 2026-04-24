#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

from fuzzer_protocol import *

if __name__ == "__main__":
    packets = []

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

    ### Destroy:
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

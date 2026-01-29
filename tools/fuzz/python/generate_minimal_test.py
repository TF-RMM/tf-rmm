#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

from fuzzer_protocol import *

if __name__ == "__main__":
    packets = []

    packets.append(Version(req=0x00010000))
    packets.append(Features(index=1))

    rd = 0
    rec = 1

    packets.append(AllocateGranule(index=rd))
    packets.append(AllocateGranule(index=rec))

    packets.append(GranuleDelegate(index=rd))
    packets.append(GranuleDelegate(index=rec))

    packets.append(GranuleUndelegate(index=rd))
    packets.append(GranuleUndelegate(index=rec))

    import os
    import sys

    os.makedirs(os.path.dirname(sys.argv[1]), exist_ok=True)
    with open(sys.argv[1], "wb") as f:
        for p in packets:
            rmi_packet = RMI() / p
            f.write(raw(rmi_packet))

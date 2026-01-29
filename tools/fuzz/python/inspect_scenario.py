#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

from fuzzer_protocol import *


class RMIPacketList(Packet):
    name = "RMI packet list"
    fields_desc = [
        LEFieldLenField("len", None, length_of="packets", adjust=lambda pkt, x: x - 8),
        PacketListField("packets", [], RMI, length_from=lambda pkt: pkt.len - 2)
    ]


# bind_layers(RMIPacketList, RMI)

def inspect_file(file):
    with open(file, "rb") as f:
        data = f.read()
        # print(data)

    # data = pack("<I", len(data)) + data
    # print(data)

    while data.__len__():
        packet = RMI(data)
        fields = packet.payload.payload.original
        # print(fields)
        packet.show()
        data = fields


def inspect_folder(folder):
    for filename in os.listdir(folder):
        file_path = os.path.join(folder, filename)
        if os.path.isfile(file_path):  # Ensure it's a file
            inspect_file(file_path)


if __name__ == "__main__":
    import sys

    path = sys.argv[1]

    if os.path.isfile(path):  # Ensure it's a file
        inspect_file(path)
    else:
        inspect_folder(path)

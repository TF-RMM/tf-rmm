#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

from fuzzer_protocol import *


if __name__ == "__main__":
    packets = []

    # Granule index assignments
    rd = 0
    calling_rec = 1
    target_rec = 2
    realm_params = 3
    rec_params = 4
    rec_run = 5
    rtt_base = 6

    for idx in [rd, calling_rec, target_rec, realm_params, rec_params,
                rec_run, rtt_base]:
        packets.append(AllocateGranule(index=idx))

    for idx in [rd, calling_rec, target_rec, rtt_base]:
        packets.append(GranuleDelegate(index=idx))

    packets.append(
        RealmCreate(rd_index=rd, param_index=realm_params,
                    s2sz=0x30, num_bps=1, num_wps=1,
                    rtt_base_index=rtt_base, rtt_num_start=1))
    packets.append(SroDonate(count=0))
    packets.append(SroContinue(flags=0))

    # The calling REC is runnable; the CPU_ON target REC is initially off.
    packets.append(RecCreate(rd_index=rd, rec_index=calling_rec,
                             param_index=rec_params, flags=1, mpidr=0))
    packets.append(SroDonate(count=0))
    packets.append(SroContinue(flags=0))

    packets.append(RecCreate(rd_index=rd, rec_index=target_rec,
                             param_index=rec_params, flags=0, mpidr=1))
    packets.append(SroDonate(count=0))
    packets.append(SroContinue(flags=0))

    packets.append(RealmActivate(rd_index=rd))

    # SMCCC passes the function identifier in W0. X0[63:32] is deliberately
    # non-zero here. Before the PSCI completion fix, initial dispatch treated
    # this as SMC64_PSCI_CPU_ON (0xC4000003), but psci_complete_request()
    # compared the full X0 value and asserted.
    malformed_psci_cpu_on = (0x1 << 32) | 0xC4000003
    packets.append(RsiCall(fid=malformed_psci_cpu_on,
                           arg1=1,       # target REC MPIDR
                           arg2=0,       # protected entry point
                           arg3=0x100))  # context ID
    packets.append(RecEnter(rec_index=calling_rec, run_index=rec_run))
    packets.append(PsciComplete(calling_rec=calling_rec,
                                target_rec=target_rec,
                                status=0))

    import os
    import sys

    os.makedirs(os.path.dirname(sys.argv[1]), exist_ok=True)
    with open(sys.argv[1], "wb") as f:
        for p in packets:
            rmi_packet = RMI() / p
            f.write(raw(rmi_packet))

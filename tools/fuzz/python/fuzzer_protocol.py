#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
from scapy.all import *


class RMI(Packet):
    name = "RMI"
    fields_desc = [
        ByteField("command", 0)
    ]


class Version(Packet):
    name = "Version"
    fields_desc = [
        LELongField("req", 0x00010000)
    ]


class GranuleDelegate(Packet):
    name = "Granule delegate"
    fields_desc = [
        ByteField("index", 0)
    ]


class GranuleUndelegate(Packet):
    name = "Granule undelegate"
    fields_desc = [
        ByteField("index", 0)
    ]


class RttDataMapInit(Packet):
    name = "Rtt data map init"
    fields_desc = [
        ByteField("rd_index", 0),
        ByteField("data_index", 0),
        LELongField("ipa", 0),
        ByteField("src", 0),
        LELongField("flags", 0)
    ]


class RttDataUnmap(Packet):
    name = "Rtt data unmap"
    fields_desc = [
        ByteField("rd_index", 0),
        LELongField("base", 0),
        LELongField("top", 0),
        LELongField("flags", 0)
    ]


class RttDataMap(Packet):
    name = "Rtt data map"
    fields_desc = [
        ByteField("rd_index", 0),
        LELongField("base", 0),
        LELongField("top", 0),
        LELongField("flags", 0),
        LELongField("oaddr", 0)
    ]


class RealmActivate(Packet):
    name = "Realm activate"
    fields_desc = [
        ByteField("rd_index", 0),
    ]


class RealmCreate(Packet):
    name = "Realm create"
    fields_desc = [
        ByteField("rd_index", 0),
        ByteField("param_index", 0),
        LELongField("flags", 0),
        LEIntField("s2sz", 0),
        LEIntField("sve_vl", 0),
        LEIntField("num_bps", 0),
        LEIntField("num_wps", 0),
        LEIntField("pmu_num_ctrs", 0),
        ByteField("hash_algo", 0),
        ByteField("rpv", 0),
        ByteField("rtt_base_index", 0),
        LELongField("rtt_level_start", 0),
        LEIntField("rtt_num_start", 0)
    ]


class RealmDestroy(Packet):
    name = "Realm destroy"
    fields_desc = [
        ByteField("rd_index", 0)
    ]


class RecCreate(Packet):
    name = "Rec create"
    fields_desc = [
        ByteField("rd_index", 0),
        ByteField("rec_index", 0),
        ByteField("param_index", 0),
        LELongField("flags", 0),
        LELongField("mpidr", 0),
    ]


class RecDestroy(Packet):
    name = "Rec destroy"
    fields_desc = [
        ByteField("rec_index", 0),
    ]


class RecEnter(Packet):
    name = "Rec enter"
    fields_desc = [
        ByteField("rec_index", 0),
        ByteField("run_index", 0),
    ]


class RTTCreate(Packet):
    name = "RTT create"
    fields_desc = [
        ByteField("rd_index", 0),
        ByteField("rtt_index", 0),
        LELongField("ipa", 0),
        LEIntField("level", 0)
    ]


class RTTDestroy(Packet):
    name = "RTT destroy"
    fields_desc = [
        ByteField("rd_index", 0),
        LELongField("ipa", 0),
        LEIntField("level", 0)
    ]


class RTTMapUnprotected(Packet):
    name = "RTT Map Unprotected"
    fields_desc = [
        ByteField("rd_index", 0),
        LELongField("ipa", 0),
        LEIntField("level", 0),
        LELongField("desc", 0),
    ]


class RTTReadEntry(Packet):
    name = "RTT Read Entry"
    fields_desc = [
        ByteField("rd_index", 0),
        LELongField("ipa", 0),
        LEIntField("level", 0),
    ]


class RTTUnmapUnprotected(Packet):
    name = "RTT Unmap Unprotected"
    fields_desc = [
        ByteField("rd_index", 0),
        LELongField("ipa", 0),
        LEIntField("level", 0),
    ]


class PsciComplete(Packet):
    name = "PSCI complete"
    fields_desc = [
        ByteField("calling_rec", 0),
        ByteField("target_rec", 0),
        LEIntField("status", 0)
    ]


class Features(Packet):
    name = "Features"
    fields_desc = [
        LEIntField("index", 1)
    ]


class RttFold(Packet):
    name = "RTT Fold"
    fields_desc = [
        ByteField("rd_index", 0),
        LELongField("ipa", 0),
        LEIntField("level", 0),
    ]


class RttInitRipas(Packet):
    name = "RTT Init ripas"
    fields_desc = [
        ByteField("rd_index", 0),
        LELongField("base", 0),
        LELongField("top", 0)
    ]


class RttSetRipas(Packet):
    name = "RTT set ripas"
    fields_desc = [
        ByteField("rd_index", 0),
        ByteField("rec_index", 0),
        LELongField("base", 0),
        LELongField("top", 0)
    ]


class AllocateGranule(Packet):
    name = "Allocate granule"
    fields_desc = [
        ByteField("index", 0)
    ]


class RmmConfigGet(Packet):
    name = "Rmm config get"
    fields_desc = [
        ByteField("config_index", 0)
    ]


class RmmConfigSet(Packet):
    name = "Rmm config set"
    fields_desc = [
        ByteField("config_index", 0)
    ]


class GranuleTrackingGet(Packet):
    name = "Granule tracking get"
    fields_desc = [
        ByteField("granule_index", 0)
    ]


class SroDonate(Packet):
    name = "Sro donate"
    fields_desc = [
        ByteField("count", 0),
    ]


class SroReclaim(Packet):
    name = "Sro reclaim"
    fields_desc = [
        ByteField("list_entries", 16),
    ]


class SroContinue(Packet):
    name = "Sro continue"
    fields_desc = [
        LELongField("flags", 0),
    ]


# fid: 10xC4000150 - 0xC4000169
bind_layers(RMI, AllocateGranule, command=99)

bind_layers(RMI, Version, command=0)
bind_layers(RMI, GranuleDelegate, command=1)
bind_layers(RMI, GranuleUndelegate, command=2)
bind_layers(RMI, RttDataMapInit, command=3)
# command 4 removed (was DataCreateUnknown)
bind_layers(RMI, RttDataUnmap, command=5)
# < reserved command 6>
bind_layers(RMI, RealmActivate, command=7)
bind_layers(RMI, RealmCreate, command=8)
bind_layers(RMI, RealmDestroy, command=9)
bind_layers(RMI, RecCreate, command=10)
bind_layers(RMI, RecDestroy, command=11)
bind_layers(RMI, RecEnter, command=12)
bind_layers(RMI, RTTCreate, command=13)
bind_layers(RMI, RTTDestroy, command=14)
bind_layers(RMI, RTTMapUnprotected, command=15)
# < reserved command 16>
bind_layers(RMI, RTTReadEntry, command=17)  # <I> s2tte states uncovered
bind_layers(RMI, RTTUnmapUnprotected, command=18)
# < reserved command 19>
bind_layers(RMI, PsciComplete, command=20)
bind_layers(RMI, Features, command=21)
bind_layers(RMI, RttFold, command=22)  # <I> s2tte states uncovered
# command 23 removed (was RecAuxCount)
bind_layers(RMI, RttInitRipas, command=24)
bind_layers(RMI, RttSetRipas, command=25)
bind_layers(RMI, RttDataMap, command=26)
bind_layers(RMI, RmmConfigGet, command=27)
bind_layers(RMI, RmmConfigSet, command=28)
bind_layers(RMI, GranuleTrackingGet, command=29)
bind_layers(RMI, SroDonate, command=30)
bind_layers(RMI, SroReclaim, command=31)
bind_layers(RMI, SroContinue, command=32)

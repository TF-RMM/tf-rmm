#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
import json
import os
import subprocess

import click

schedules = ["explore", "fast", "exploit", "seek", "rare", "mmopt", "coe", "lin", 'quad']
corpora = ["default", "invalid", "min", "pmu", "ripas", "rtt", "rtt-fold"]

fuzz_root = "_Fuzz"
fuzz_out = f"{fuzz_root}/aflout"
fuzz_builddir = f"{fuzz_root}/builds"
fuzz_benchdir = f"{fuzz_root}/bench"
ncpu = os.cpu_count()


def exec_single(cmd):
    fin_cmd = f"bash -c '. ./tools/fuzz/fuzz.env ;{cmd}'"
    print(fin_cmd)
    subprocess.run(fin_cmd, shell=True, check=True)


def exec_byobu(ses_dict):
    base = "byobu new-session -d -s fuzzer -n monitor 'btop' \\\n"
    for name, fuzz_cmd in ses_dict.items():
        wrapped_cmd = f"bash -c '{fuzz_cmd}; exec $SHELL'"
        base = base + f"\; new-window -n {name} \"{wrapped_cmd}\" \\\n"
    fin_cmd_str = base  # +    "\; attach"
    print(fin_cmd_str)
    subprocess.run(fin_cmd_str, shell=True, check=True)


def exec_no_mux(ses_list):
    base = ""
    for name, fuzz_cmd in ses_list.items():
        base = base + f"{fuzz_cmd} & \\\n"
    fin_cmd_str = base + "wait"
    print(fin_cmd_str)
    subprocess.run(fin_cmd_str, shell=True, check=True)


@click.option('-v', '--variants', type=click.Choice(['corpus', 'schedule']), required=True)
@click.command(help='Build multiple targets (consecutively)')
def multibuild(variants):
    if variants == 'corpus':
        variants = corpora
    else:
        variants = schedules

    cmds = ""
    for variant in variants:
        cmd = f"fuzzbuild 1 {variant} && "
        cmds += cmd
    cmds += "wait"
    print(json.dumps(cmds, indent=4))
    # Cannot run parallel
    exec_single(cmds)


@click.option('-v', '--variants', type=click.Choice(['corpus', 'schedule']), required=True)
@click.command(help='Get afl-plot for specified build variants')
def get_plots(variants):
    variants = corpora if variants == 'corpus' else schedules
    commands = {}
    for variant in variants:
        cmd = f"afl-plot {fuzz_out}/{variant}/s-{variant} {fuzz_benchdir}/{variant}"
        commands[variant] = cmd

    print(json.dumps(commands, indent=4))
    exec_no_mux(commands)


@click.option('-v', '--variants', type=click.Choice(['corpus', 'schedule']), required=True)
@click.command(help='Get coverage report for specified build variants')
def get_coverage(variants):
    variants = corpora if variants == 'corpus' else schedules
    cmds = ""
    for variant in variants:
        cmd = f"cmake --build {fuzz_builddir}/{variant} -- run-coverage && "
        cmds += cmd
    cmds += "wait"

    print(json.dumps(cmds, indent=4))
    exec_single(cmds)


@click.option('-b', '--build_name', required=True)
@click.option('-w', '--workers', type=int, default=4)
@click.option('-V', '--duration', type=int, default=0)
@click.option('-t', '--timeout', type=int, default=1000)
@click.option('--no-ui', is_flag=True, default=False, help="Run AFL without status screen")
@click.option('--mix', is_flag=True, default=False, help="Use different schedules for each worker")
@click.option('--mux', is_flag=True, default=False, help="Run sessions with terminal multiplexer")
@click.option('--sim', is_flag=True, default=False, help="Simulate - Print the commands without executing")
@click.command(help='Spawn multiple fuzzers')
def spawn(build_name, workers, duration, timeout, no_ui, mix, mux, sim):
    sessions = {}

    io = f"-i {fuzz_builddir}/{build_name}/smc_corpus -o {fuzz_out}/{build_name}"
    target = f" -- ./{fuzz_builddir}/{build_name}/Debug/rmm.elf"

    params = f"-t {timeout} -a binary"
    main_params = ""
    snd_params = ""

    env = ""

    if duration > 0:
        main_params = params + f" -V {duration + 5} "
        snd_params = params + f" -V {duration} "

    if no_ui:
        env += "AFL_NO_UI=1"

    # Main worker:
    main_name = f"m-{build_name}"
    main_affinity = int(ncpu / 5)

    main_cmd = f"{env} afl-fuzz {io} -M {main_name} -b {main_affinity} {main_params} {target}"
    sessions[main_name] = main_cmd

    # Secondary workers:
    for i in range(1, workers):
        snd_name = f"s{i}-{build_name}"
        snd_affinity = (main_affinity + 5 * i) % ncpu
        sched = ""

        # if mix_schedule set, choose a schedule from list starting with mmopt (index 5 = i+4)
        if mix:
            sched = f"-P {schedules[(i + 4) % len(schedules)]}"

        snd_cmd = f"{env} afl-fuzz {io} -S {snd_name} -b {snd_affinity} {snd_params} {sched} {target}"
        sessions[snd_name] = snd_cmd

    print(json.dumps(sessions, indent=4))
    if sim:
        return
    if mux:
        exec_byobu(sessions)
    else:
        exec_no_mux(sessions)


@click.option('-V', '--duration', type=int, default=1000)
@click.option('-t', '--timeout', type=int, default=1000)
@click.option('--sim', is_flag=True, default=False, help="Simulate - Print the commands without executing")
@click.command(help='Benchmark corpora')
def bench_corpora(duration, timeout, sim):
    sessions = {}
    main_affinity = int(ncpu / 5)
    params = f"-t {timeout} -V {duration} -a binary"

    i = 0
    for corpus in corpora:
        target = f" -- ./{fuzz_builddir}/{corpus}/Debug/rmm.elf"

        # move desire corpus to single_corpus directory
        corp_dir = f"{fuzz_builddir}/{corpus}/single_corpus/"
        move_cmd = f"mkdir {corp_dir} ; mv {fuzz_builddir}/{corpus}/smc_corpus/{corpus}.bin {corp_dir} ; "

        snd_name = f"s-{corpus}"
        snd_affinity = (main_affinity + 5 * i) % ncpu
        i += 1

        snd_cmd = f"afl-fuzz -i {corp_dir} -o {fuzz_out}/{corpus} -S {snd_name} -b {snd_affinity} {params} {target}"
        sessions[snd_name] = move_cmd + snd_cmd

    print(json.dumps(sessions, indent=4))
    if sim:
        return
    else:
        exec_byobu(sessions)


@click.option('-V', '--duration', type=int, default=1000)
@click.option('-t', '--timeout', type=int, default=1000)
@click.option('--sim', is_flag=True, default=False, help="Simulate - Print the commands without executing")
@click.command(help='Benchmark schedules')
def bench_sched(timeout, duration, sim):
    sessions = {}
    main_affinity = int(ncpu / 5)
    params = f"-t {timeout} -V {duration} -a binary"

    i = 0
    for sched in schedules:
        target = f" -- ./_Fuzz/builds/{sched}/Debug/rmm.elf"
        snd_name = f"s-{sched}"
        snd_affinity = (main_affinity + 5 * i) % ncpu
        i += 1

        snd_cmd = (
            f"afl-fuzz -i {fuzz_builddir}/{sched}/smc_corpus -o {fuzz_out}/{sched} -S {snd_name} -b {snd_affinity} {params} -p {sched} {target}")
        sessions[snd_name] = snd_cmd

    print(json.dumps(sessions, indent=4))
    if sim:
        return
    else:
        exec_byobu(sessions)


@click.command(cls=click.Group, context_settings=dict(help_option_names=['-h', '--help']))
def multirun():
    pass


multirun.add_command(multibuild)
multirun.add_command(spawn)
multirun.add_command(bench_corpora)
multirun.add_command(bench_sched)
multirun.add_command(get_plots)
multirun.add_command(get_coverage)

if __name__ == "__main__":
    multirun()

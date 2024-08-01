#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

"""
Script for creating a bin file from the compiled app's elf file.

The name of the elf sections that are expected and added in the output binary
are hardcoded in the script. The resulting binary consists of a header which is
page in size and content of selected sections which are appended after the
header.
```
+----------------------+
|                      |
|       Header         |
|                      |
+----------------------+
|                      |
| Content of section 1 |
|                      |
+----------------------+
|                      |
           ...
|                      |
+----------------------+
|                      |
|Content of section n  |
|                      |
+----------------------+
```
"""

from argparse import ArgumentParser
from collections import namedtuple
import logging
import struct


from elftools.elf.elffile import ELFFile

INDENTATION = "\t"
APP_HEADER_MAGIC = 0x000E10ABB4EAD000  # El0 APP HEAD
HEADER_VERSION_MAJOR = 0
HEADER_VERSION_MINOR = 1
# TODO: get page size from command line
PAGE_SIZE = 4096
APP_HEADER_RESERVED_BYTES = 10 * 8
APP_NAME_BUF_SIZE = 32

HEADER_VERSION = (HEADER_VERSION_MAJOR << 16) | HEADER_VERSION_MINOR

# The header format needs to match the header in
# "app/common/framework/include/fake_host/app_header_structures.h" file as defined in
# 'struct el0_app_header'
BIN_HEADER_FORMAT = "".join(
    [
        "<",  # little endian
        "Q",  # uint64_t padding;
        "Q",  # uint64_t app_header_magic;
        "L",  # uint32_t app_header_version;
        f"{APP_NAME_BUF_SIZE}s" # const char app_name[APP_NAME_BUF_SIZE];
        "L",  # uint32_t app_id;
        "Q",  # uint64_t app_len; /* including header */
        "Q",  # uintptr_t section_text_offset;
        "Q",  # uintptr_t section_text_va;
        "Q",  # size_t section_text_size;
        "Q",  # uintptr_t section_rodata_offset;
        "Q",  # uintptr_t section_rodata_va;
        "Q",  # size_t section_rodata_size;
        "Q",  # uintptr_t section_data_offset;
        "Q",  # uintptr_t section_data_va;
        "Q",  # size_t section_data_size;
        "Q",  # uintptr_t section_bss_va ;
        "Q",  # size_t section_bss_size;
        "Q",  # section_shared_va;
        "Q",  # size_t stack_page_count;
        "Q",  # size_t heap_page_count;
        f"{APP_HEADER_RESERVED_BYTES}s"  # reserved
        "Q",  # uint64_t app_header_magic2;
    ]
)

SectionParams = namedtuple("SectionParams", ["name", "emit"])
SectionData = namedtuple("SectionData", ["params", "vma", "size", "data"])


def get_section(sections, idx, name):
    """Returns the section in the sections list at the given index.

    The function makes sure that the section at the specified index has the
    specified name.
    """
    if sections[idx].params.name != name:
        logging.error(
            f"At idx {idx} section name '{sections[idx].params.name}' doesn't match '{name}'"
        )
        assert False
    return sections[idx]

def get_app_name_bytes(app_name):
    if len(app_name) >= (APP_NAME_BUF_SIZE):
        app_name = app_name[:APP_NAME_BUF_SIZE -1]
    b_appname = app_name.encode()
    assert(len(b_appname) < APP_NAME_BUF_SIZE)
    return bytes().join([b_appname, bytes([0] * (APP_NAME_BUF_SIZE - len(b_appname)))])

def emit_bin_file_header(out_bin_file, app_name, app_id, app_len, stack_page_count, heap_page_count, sections):
    """Emit the bin file header that will be parsed by the RMM code"""
    text_section = get_section(sections, 0, ".text")
    rodata_section = get_section(sections, 1, ".rodata")
    data_section = get_section(sections, 2, ".data")
    bss_section = get_section(sections, 3, ".bss")
    shared_section = get_section(sections, 4, ".shared")
    text_offset = 0
    rodata_offset = text_offset + text_section.size
    data_offset = rodata_offset + rodata_section.size
    header = struct.pack(
        BIN_HEADER_FORMAT,
        0,
        APP_HEADER_MAGIC,
        HEADER_VERSION,
        get_app_name_bytes(app_name),
        app_id,
        app_len,
        0,  # text
        text_section.vma,
        text_section.size,
        rodata_offset,  # rodata
        rodata_section.vma,
        rodata_section.size,
        data_offset,  # data
        data_section.vma,
        data_section.size,
        bss_section.vma,  # bss
        bss_section.size,
        shared_section.vma,  # shared
        stack_page_count,  # stack
        heap_page_count,  # heap
        bytes(APP_HEADER_RESERVED_BYTES),
        APP_HEADER_MAGIC,
    )
    logging.info(f"Emitting binary header, {len(header)} bytes.")
    logging.info(
        f"    app_header_magic: #1={APP_HEADER_MAGIC:016x}, #2={APP_HEADER_MAGIC:016x}"
    )
    logging.info(f"    app_name               =   {app_name:16}")
    logging.info(f"    app_header_version     =   0x{HEADER_VERSION:16x}")
    logging.info(f"    app_id                 =     {app_id:16}")
    logging.info(f"    app_len                =   0x{app_len:16x}")

    logging.info("    section  |   offset |               va |     size")
    logging.info("    ---------|----------|------------------|---------")
    logging.info(
        f"    text     | {0:8x} | {text_section.vma:16x} | {text_section.size:8x}"
    )
    logging.info(
        f"    rodata   | {rodata_offset:8x} | {rodata_section.vma:16x} | {rodata_section.size:8x}"
    )
    logging.info(
        f"    data     | {data_offset:8x} | {data_section.vma:16x} | {data_section.size:8x}"
    )
    logging.info(
        f"    bss      |      N/A | {bss_section.vma:16x} | {bss_section.size:8x}"
    )
    logging.info(f"    shared   |      N/A | {shared_section.vma:16x} | {PAGE_SIZE:8x}")
    logging.info(
        f"    stack    |      N/A |              N/A | {stack_page_count*PAGE_SIZE:8x}"
    )
    logging.info(
        f"    heap     |      N/A |              N/A | {heap_page_count*PAGE_SIZE:8x}"
    )

    out_bin_file.write(header)

    # emit padding to keep the app binary page aligned
    assert len(header) < PAGE_SIZE
    out_bin_file.write(bytearray([0] * (PAGE_SIZE - len(header))))

    return PAGE_SIZE


def emit_section_data(out_bin_file, sections):
    """Emitting content of a section

    Return the number of bytes emitted for this section
    """
    bytes_emitted = 0
    for section in sections:
        if section.data is not None and section.params.emit:
            logging.info(
                f"Emitting section '{section.params.name}', {len(section.data)} bytes."
            )
            out_bin_file.write(section.data)
            bytes_emitted += len(section.data)
    return bytes_emitted


def calc_sections_size(sections):
    """Calculates the length of the sections part of the bin"""
    length = PAGE_SIZE  # accounting for header
    for section in sections:
        if section.data is not None and section.params.emit:
            length += len(section.data)
    if length % PAGE_SIZE != 0:
        length += PAGE_SIZE - (length % PAGE_SIZE)
    return length


def emit_bin_file(out_bin_file_name, app_name, app_id, stack_page_count, heap_page_count, sections):
    """Write the bin file"""
    bytes_emitted = 0
    with open(out_bin_file_name, "wb") as out_bin_file:
        # Calculate the length of the bin file payload to be written in to the header
        app_len = calc_sections_size(sections)
        # Write the bin header
        bytes_emitted += emit_bin_file_header(
            out_bin_file, app_name, app_id, app_len, stack_page_count, heap_page_count, sections
        )
        # Write the sections that needs to be emitted
        bytes_emitted += emit_section_data(out_bin_file, sections)

        # Add padding so that the bin file is aligned to page boundary
        padding_length = PAGE_SIZE - (((bytes_emitted + PAGE_SIZE - 1) % PAGE_SIZE) + 1)
        assert (bytes_emitted + padding_length) % PAGE_SIZE == 0
        assert padding_length < PAGE_SIZE
        if padding_length:
            out_bin_file.write(bytearray([0] * padding_length))
            bytes_emitted += padding_length
        assert bytes_emitted == app_len


def get_sections_data(elffile, sections_params):
    elf_section_idx = 0
    section_idx = 0
    sections_found = []

    expected_section_names = [section.name for section in sections_params]

    # Assume that the interesting sections are in the expected order
    while elf_section_idx < elffile.num_sections() and section_idx < len(sections_params):
        elf_section = elffile.get_section(elf_section_idx)

        if elf_section.name not in expected_section_names[section_idx:]:
            logging.info(
                f"Skipping section {elf_section.name}, ({elf_section.data_size} bytes)"
            )
            elf_section_idx += 1
            if elf_section_idx == elffile.num_sections():
                break
            continue

        section_params = sections_params[section_idx]

        if elf_section.name != section_params.name:
            logging.info(
                f"Section {expected_section_names[section_idx]} not found in the elf file"
            )
            section_idx += 1
            continue

        assert elf_section.name == section_params.name

        logging.info(f"Found section {elf_section.name} size={elf_section.data_size}")

        section_data = SectionData(
            params=section_params,
            vma=elf_section.header["sh_addr"],
            size=elf_section.data_size,
            data=elf_section.data(),
        )
        sections_found.append(section_data)
        assert section_data.size == len(section_data.data)

        elf_section_idx += 1
        section_idx += 1

    while elf_section_idx < elffile.num_sections():
        elf_section = elffile.get_section(elf_section_idx)
        logging.info(
            f"Skipping section {elf_section.name}, ({elf_section.data_size} bytes)"
        )
        elf_section_idx += 1

    while section_idx < len(sections_params):
        section = sections_params[section_idx]
        logging.info(f"Section {section.name} not found in the elf file")
        section_idx += 1

    return sections_found


def parse_elf_file(elf_file_name):
    """parse the elf file

    returns the relevant sections' data found in the file
    """
    with open(elf_file_name, "rb") as in_file:
        sections = [
            SectionParams(".text", emit=True),
            SectionParams(".rodata", emit=True),
            SectionParams(".data", emit=True),
            SectionParams(".bss", emit=False),
            SectionParams(".shared", emit=False),
        ]

        elffile = ELFFile(in_file)

        logging.info(f"{elf_file_name} has {elffile.num_sections()} sections.")

        # Assume that the interesting sections are in the expected order
        return get_sections_data(elffile, sections)


def main():
    """Main function of the script"""
    logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.DEBUG)

    parser = ArgumentParser(description="Generate app data files for packaging.")
    parser.add_argument(
        "--elf-file", type=str, required=True, help="elf file to generate raw data for"
    )
    parser.add_argument(
        "--app-id",
        type=lambda v: int(v, 0),
        required=True,
        help="The ID of the application used in the RMM code",
    )
    parser.add_argument(
        "--app-name",
        required=True,
        help="The name of the app",
    )
    parser.add_argument(
        "--stack-page-count",
        type=int,
        required=True,
        help="The stack size required by the application",
    )
    parser.add_argument(
        "--heap-page-count",
        type=int,
        required=True,
        help="The heap size required by the application (0 is valid)",
    )
    parser.add_argument(
        "--out-bin",
        type=str,
        required=True,
        help="application data for the bin generation",
    )
    args = parser.parse_args()

    logging.info(f"Processing {args.elf_file}, app_name='{args.app_name}', app_id={args.app_id:x}")
    sections = parse_elf_file(args.elf_file)
    emit_bin_file(args.out_bin, args.app_name, args.app_id, args.stack_page_count, args.heap_page_count, sections)


if __name__ == "__main__":
    main()

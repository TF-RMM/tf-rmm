#!/usr/bin/env python3
#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#
"""
A static analysis tool for checking for banned API's in C, Header and
Assembly files.

To ignore a check for a banned API include `BANNED-API-CHECK[IGNORE]`
on the line above the banned API as a code comment.
"""
from argparse import ArgumentParser, Namespace
import logging
import re
import sys
from os import access, R_OK
from os.path import isfile, splitext

accepted_files: tuple = (".c", ".h", ".S")  # A tuple of the accepted file types.

# A tuple of ignored directories.
ignored_dirs: tuple = ("tools", "docs")


def file_readable(file: str, ignored_files: list | None = None) -> bool:
    """Checks that the file is readable and can be checked.

    Args:
        file: The path to the file.
        ignored_files = None: A list of the files to ignore checking for Banned APIs.

    Returns:
        If the file can be read.
    """
    if file in ignored_dirs:
        logging.warning(f"{file}: File is ignored directory list.")
        return False

    if ignored_files:
        if file in ignored_files:
            logging.warning(f"{file}: File is in the ignore list.")
            return False

    if not isfile(file):
        logging.warning(f"{file}: File not found.")
        return False

    if not access(file, R_OK):
        logging.warning(f"{file}: File not readable.")
        return False

    if splitext(file)[1] not in accepted_files:
        logging.warning(f"{file}: File is not accepted, must be a .c, .h or .S file.")
        return False

    return True


def file_contents_list(path: str) -> list:
    """Fetch the contents of the file.

    Args:
        path: The path to the file.

    Returns:
        A list of each line in the file.
    """
    try:
        with open(path, "r", encoding="utf-8") as f:
            return [line.rstrip("\n") for line in f]

    except Exception:
        logging.exception(f"{path}: ERROR while parsing.")
        return []


def strip_comments(file_contents: list) -> list:
    """Strip C comments while preserving code and line numbering."""
    in_block_comment: bool = False
    stripped_lines: list = []

    for line in file_contents:
        i: int = 0
        line_out: list[str] = []
        in_string: bool = False
        in_char: bool = False

        while i < len(line):
            ch = line[i]
            nxt = line[i + 1] if (i + 1) < len(line) else ""

            if in_block_comment:
                if (ch == "*") and (nxt == "/"):
                    in_block_comment = False
                    i += 2
                    continue
                i += 1
                continue

            if in_string:
                line_out.append(ch)
                if (ch == "\\") and ((i + 1) < len(line)):
                    line_out.append(line[i + 1])
                    i += 2
                    continue
                if ch == "\"":
                    in_string = False
                i += 1
                continue

            if in_char:
                line_out.append(ch)
                if (ch == "\\") and ((i + 1) < len(line)):
                    line_out.append(line[i + 1])
                    i += 2
                    continue
                if ch == "'":
                    in_char = False
                i += 1
                continue

            if ch == "\"":
                in_string = True
                line_out.append(ch)
                i += 1
                continue

            if ch == "'":
                in_char = True
                line_out.append(ch)
                i += 1
                continue

            if (ch == "/") and (nxt == "/"):
                break

            if (ch == "/") and (nxt == "*"):
                in_block_comment = True
                i += 2
                continue

            line_out.append(ch)
            i += 1

        stripped_lines.append("".join(line_out))

    return stripped_lines


def compile_banned_patterns(banned_apis: list) -> list:
    """Compile patterns for banned API function-like invocations."""
    patterns: list = []

    for api in banned_apis:
        if api:
            patterns.append(
                (
                    api,
                    re.compile(rf"(?<![A-Za-z0-9_]){re.escape(api)}\s*\("),
                )
            )

    return patterns


def check_banned_apis(
    file: str, banned_apis: list, ignored_files: list | None = None
) -> dict:
    """Checks a file for banned APIs.

    Args:
        file: The file that is being checked for banned APIs.
        ignored_files = None: A list of the files to ignore checking for Banned APIs.

    Returns:
        A dictionary of lines containing banned APIs.
    """
    print("Checking file: " + file)
    if not file_readable(file, ignored_files):
        return {}

    f_list: list = file_contents_list(file)
    stripped_lines: list = strip_comments(f_list)
    banned_patterns: list = compile_banned_patterns(banned_apis)
    error_lines: dict[str, str] = (
        {}
    )  # A dictionary of the lines containing banned APIs.

    for idx, line in enumerate(stripped_lines):
        if not line.strip():
            continue

        matched_api: str | None = None
        for api, pattern in banned_patterns:
            if pattern.search(line):
                matched_api = api
                break

        if matched_api is not None:
            if (idx > 0) and ("BANNED-API-CHECK[IGNORE]" in f_list[idx - 1]):
                # Check for the ignore marker on the line above the banned API use.
                logging.warning(f"{file}: Ignoring check at line `{idx + 1}`")
                continue

            error_lines.update(
                {
                    f'Banned API: \033[0;31m"{matched_api}"\033[0m found at "{file}, line {idx + 1}"': str(
                        f_list[idx]
                    ).strip()
                }
            )

    return error_lines


def print_error_and_exit(line_dict: dict) -> None:
    """Prints out total number of errors and ends execution with return code.

    Args:
        line_dict: A dictionary of errors.
    """
    total_errors: int = 0
    for key, line in line_dict.items():
        print(key, "\033[0;31m" + line + "\033[0m")
        total_errors += 1

    if total_errors:
        print("\033[0;31m" + f"total errors: {total_errors} found" + "\033[0m")
        sys.exit(1)

    print(f"\033[0;32mNo errors found\033[0m")


# main
if __name__ == "__main__":
    ap: ArgumentParser = ArgumentParser(description="Check for banned APIs")
    ap.add_argument("files", nargs="*", help="Check files.")
    ap.add_argument(
        "--banned_apis",
        nargs="*",
        help="REQUIRED: The file of banned APIs.",
        required=True,
    )
    ap.add_argument(
        "--ignore_files",
        nargs="*",
        help="OPTIONAL: The files to be ignored.",
    )

    args: Namespace = ap.parse_args()
    errors_dict: dict[str, str] = {}

    ignored_files: list | None = None

    if args.ignore_files:
        with open(args.ignore_files[0], "r", encoding="utf-8") as f:
            ignored_files = [l.strip() for l in f]

    with open(args.banned_apis[0], "r", encoding="utf-8") as f:
        banned_apis: list = [api.strip() for api in f]

    for file in args.files:
        api_check = check_banned_apis(file, banned_apis, ignored_files)
        errors_dict |= api_check

    print_error_and_exit(errors_dict)

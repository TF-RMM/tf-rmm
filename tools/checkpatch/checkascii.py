#!/usr/bin/env python3
#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#
"""
A static analysis tool for checking for non ASCII characters in C, Header, Assembly
and C++ files.

To ignore a check for a non ascii characters include `NON-ASCII-CHECK[IGNORE]`
on the line above the non ascii character as a code comment.
"""

from argparse import ArgumentParser, Namespace
import re
import sys
from os import access, R_OK
from os.path import isfile, splitext

accepted_files: tuple = (".c", ".h", ".S", ".cpp")  # Tuple of accepted file types


def file_readable(file: str) -> bool:
    """Checks that the file is readable

    Args:
        file: The path to the file

    Returns:
        If the file is valid and can be read.
    """
    if not isfile(file):
        print(f"{file}: File not found", file=sys.stderr)
        return False

    if not access(file, R_OK):
        print(f"{file}: File not readable", file=sys.stderr)
        return False

    if splitext(file)[1] not in accepted_files:
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
            return [l.strip() for l in f]

    except Exception as e:
        print(f"{path}: ERROR while parsing: {e}", file=sys.stderr)
        return []


def check_ascii(file: str) -> dict:
    """Check a file for invalid ASCII characters.

    Args:
        file: The file that is being checked for invalid ASCII characters.

    Returns:
        A dictionary of lines with invalid ASCII characters.
    """

    if not file_readable(file):
        return {}

    f_list: list = file_contents_list(file)
    error_lines: dict[str, str] = {}  # A dictionary of the lines with invalid ASCII

    in_block_comment: bool = False

    for idx, line in enumerate(f_list):
        # Track block comment state and skip lines inside /* ... */ comments.
        if in_block_comment:
            if "*/" in line:
                in_block_comment = False
            continue

        if "/*" in line:
            # Opening of a block comment; skip this line and enter block state
            # unless the comment is closed on the same line.
            if "*/" not in line:
                in_block_comment = True
            continue

        # Skip single-line // comments.
        if re.search(r"//", line):
            continue

        # The line above may carry a NON-ASCII-CHECK[IGNORE] suppression comment.
        if idx > 0 and "NON-ASCII-CHECK[IGNORE]" in f_list[idx - 1]:
            print(f"{file}: Ignoring check at line `{idx + 1}`", file=sys.stderr)
            continue

        if not str(line).isascii():
            error_lines.update(
                {
                    f'Invalid ASCII characters found at "{file}, line {idx + 1}"': str(
                        line
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

    for key, item in line_dict.items():

        error_char: str = ""
        white_space: str = len(key) * " "

        for char in item:
            if not str(char).isascii():
                total_errors += 1
                error_char += "\033[0;31m" + "^" + "\033[033m"
            else:
                error_char += " "

        print(key, item)
        print(white_space, error_char)

    if total_errors:
        print(f"total: {total_errors} errors, 0 warnings, 0 checks")
        sys.exit(1)


# main
if __name__ == "__main__":
    ap: ArgumentParser = ArgumentParser(description="Check for non ASCII characters")
    ap.add_argument("files", nargs="*", help="Check files.")

    args: Namespace = ap.parse_args()
    errors_dict: dict[str, str] = {}

    for file in args.files:
        ascii_check = check_ascii(file)
        errors_dict |= ascii_check

    print_error_and_exit(errors_dict)

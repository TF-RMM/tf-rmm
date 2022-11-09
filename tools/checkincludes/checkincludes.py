#!/usr/bin/env python3
#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
# SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
#

from argparse import ArgumentParser
import codecs
import os
import re
import sys
import logging
from os import access, R_OK
from os.path import isfile

INCLUDE_RE = re.compile(r"^\s*#\s*include\s\s*(?P<path>[\"<].+[\">])")

# exit program with rc
def print_error_and_exit(total_errors):
    if total_errors:
        print("total: " + str(total_errors) + " errors")
        sys.exit(1)
    else:
        sys.exit(0)

def include_paths(lines):
    """List all include paths in a file. Ignore starting `+` in diff mode."""
    pattern = INCLUDE_RE
    matches = (pattern.match(line) for line in lines)
    return [m.group("path") for m in matches if m]

# check if 'file' is a regular file and it is readable
def file_readable(file):
    if not isfile(file):
        print(file + ": WARNING: File not found")
        return 0

    if not access(file, R_OK):
        print(file + ": WARNING: File not readable")
        return 0

    return 1

def file_include_list(path):
    """Return a list of all include paths in a file or None on failure."""
    try:
        with codecs.open(path, encoding="utf-8") as f:
            return include_paths(f)
    except Exception:
        logging.exception(path + ": ERROR while parsing.")
        return ([])

def check_includes(file):
    """Checks whether the order of includes in the file specified in the path
    is correct or not."""
    print("Checking file: " + file)
    if not file_readable(file):
        return 0

    inc_list = file_include_list(file)

    # If there are less than 2 includes there's no need to check.
    if len(inc_list) < 2:
        return 0

    # remove leading and trailing <, >
    inc_list = [x[1:-1] for x in inc_list]

    if sorted(inc_list) != inc_list:
        print(file + ": ERROR: includes not in order. Include order should be " +
              ', '.join(sorted(inc_list)))
        return 1
    else:
        return 0

if __name__ == "__main__":
    ap = ArgumentParser(description='Check #include orders')
    ap.add_argument('files', nargs='*', help='Check files.')
    args = ap.parse_args()

    total_errors = 0
    for file in args.files:
        total_errors += check_includes(file)

    print_error_and_exit(total_errors)

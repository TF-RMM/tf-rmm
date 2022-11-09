#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

from argparse import ArgumentParser
import locale
import traceback
import sys
import re
import os
from os import access, R_OK
from os.path import isfile

SPDX_LICENSE_TAG = 'SPDX-License-Identifier:'
SPDX_COPYRIGHT_TAG = 'SPDX-FileCopyrightText:'
SPDX_DEFAULT_LICENSE = 'BSD-3-Clause'
OTHER_PROJECTS_FILES = []
PREFERRED_SPDX_LICENSE_LINE_NUMBER = 2
RST_PREFERRED_SPDX_LICENSE_LINE_NUMBER = 1

COPYRIGHT_KEYWORD = 'Copyright'
LICENSE_TAG_PATTERN = r'^(#|\*|//|..|/\*| \*)[ \t*#/]* ' + SPDX_LICENSE_TAG + r'[\w\W]*'
COPYRIGHT_TAG_PATTERN=r'^(#|\*|//|..|/\*| \*)[ \t*#/]* ' + SPDX_COPYRIGHT_TAG + r'[\w\W]*'

THIRD_PARTY_FILE_TABLE = '.. list-table:: \*\*List of files with different license\*\*'
RST_TABLE_COL1_PATTERN = r'^( |\t)*\* - [\w\W]*'
RST_TABLE_COL2_PATTERN = r'^( |\t)*- [\w\W]*'

# check if 'file' is a regular file and it is readable
def file_readable(file):
    if not isfile(file):
        print(file + ": WARNING: File not found")
        return 0

    if not access(file, R_OK):
        print(file + ": WARNING: File not readable")
        return 0

    return 1

# exit program with rc
def print_error_and_exit(total_errors):
    if total_errors:
        print("total: " + str(total_errors) + " errors")
        sys.exit(1)
    else:
        sys.exit(0)

# Get other project file and its license name
def get_other_projects_files(rst_file):
    if not file_readable(rst_file):
        return ""

    empty_line = 0
    col_num = 1
    add_row = 0

    with open(rst_file, encoding='utf-8') as fh:
        for line in fh:
            if re.search(r'^' + THIRD_PARTY_FILE_TABLE + r'$', line):
                # Parse the rst table
                for line in fh:
                    line = line.rstrip()
                    # second empty line denotes end of table
                    if empty_line > 1:
                        break

                    # ignore first empty line
                    if not line:
                        empty_line += 1
                        continue

                    if col_num == 1 and re.search(RST_TABLE_COL1_PATTERN, line):
                        col1 = line.split('-',1)[1].strip()
                        col_num = 2
                    elif col_num == 2 and re.search(RST_TABLE_COL2_PATTERN,
                                                    line):
                        col2 = line.split('-',1)[1].strip()
                        col_num = 1
                        add_row = 1
                    else:
                        print(rst_file + ": WARNING: Invalid list-table " +
                              "format in line \"" + line + "\"")
                        break

                    if add_row:
                        OTHER_PROJECTS_FILES.append(col1 + "%" + col2)
                        add_row = 0

                # after parsing the table break
                break

    return

def license_in_other_project(file, license):
    search_str = file + "%" + license
    if search_str in OTHER_PROJECTS_FILES:
        return 1
    else:
        return 0

# Check "SPDX-License-Identifier" tag is at required line number
# Check if "SPDX-License-Identifier" has a valid license
def verify_spdx_license_tag(file, line, line_number):
    errors = 0

    if re.search(r'\.rst$', file):
        preferred_line_no = RST_PREFERRED_SPDX_LICENSE_LINE_NUMBER
    else:
        preferred_line_no = PREFERRED_SPDX_LICENSE_LINE_NUMBER

    if line_number != preferred_line_no:
        print(file + ": ERROR: \"" + SPDX_LICENSE_TAG + "\" is at line:" +
              str(line_number) + " preferred line number is " +
              str(preferred_line_no))
        errors += 1

    license_string = line.split(SPDX_LICENSE_TAG)[1].strip()
    if license_string:
        license = license_string.split()[0]
        if (license != SPDX_DEFAULT_LICENSE and
            not license_in_other_project(file, license)):
            print(file + ": ERROR: Invalid license \"" + license +
                  "\" at line: " + str(line_number))
            errors += 1
    else:
        print(file + ": ERROR: License name not found at line: " +
              str(line_number))
        errors += 1

    return errors

# Check if "SPDX-FileCopyrightText:" starts with COPYRIGHT_KEYWORD
def verify_spdx_copyright_tag(file, line, line_number):
    errors = 0

    cpr_string = line.split(SPDX_COPYRIGHT_TAG)[1].strip()
    if not cpr_string or COPYRIGHT_KEYWORD != cpr_string.split()[0]:
        print(file + ": ERROR: Copyright text doesn't starts with \"" +
              COPYRIGHT_KEYWORD + " \" keyword at line: " + str(line_number))
        errors += 1

    return errors

#
# Check for tags: "SPDX-License-Identifier", "SPDX-FileCopyrightText"
#
# Check if "SPDX-FileCopyrightText" is present.
# This tag must appear be after "SPDX-License-Identifier" tag
#
def verify_spdx_headers(file):
    print("Checking file: " + file)
    if not file_readable(file):
        return 0

    lic_tag_found = 0
    cpr_tag_found = 0
    errors = 0

    # read first 25 lines
    with open(file, encoding='utf-8') as fh:
        for l in range(1, 25):
            line = fh.readline()
            if not line: # EOF
                break
            line = line.rstrip()
            if not line: # empty line
                continue

            if re.search(LICENSE_TAG_PATTERN, line):
                if lic_tag_found >= 1:
                    print(file + ": ERROR: Duplicate \"" + SPDX_LICENSE_TAG +
                          "\" tag at line: " + str(l))
                    errors += 1
                else:
                    errors += verify_spdx_license_tag(file, line, l)
                lic_tag_found += 1
                continue

            if re.search(COPYRIGHT_TAG_PATTERN, line):
                if not lic_tag_found:
                    print(file + ": ERROR: \"" + SPDX_COPYRIGHT_TAG +
                          "\" at line: " + str(l) + " must come after \""
                          + SPDX_LICENSE_TAG + "\"")
                    errors += 1
                errors += verify_spdx_copyright_tag(file, line, l)
                cpr_tag_found += 1
                continue

    if not lic_tag_found:
        print(file + ": ERROR: Missing \"" + SPDX_LICENSE_TAG + "\" tag")
        errors += 1

    if not cpr_tag_found:
        print(file + ": ERROR: Missing \"" + SPDX_COPYRIGHT_TAG + "\" tag")
        errors += 1

    if errors:
        print(file + ": " + str(errors) + " errors found")

    return errors

# main
if __name__ == '__main__':
    ap = ArgumentParser(description='Check SPDX headers')
    ap.add_argument('files', nargs='*', help='Check files.')
    ap.add_argument('-r', '--readme-rst', type=str,
                    help='path to readme.rst file', required=True)
    args = ap.parse_args()

    total_errors = 0
    readme_file = args.readme_rst

    # Parse readme file and get the list of files that have non-default license
    get_other_projects_files(readme_file)

    for file in args.files:
        total_errors += verify_spdx_headers(file)

    print_error_and_exit(total_errors)

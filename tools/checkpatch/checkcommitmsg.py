#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

"""
Script for verifying if a commit message is of the correct format.
"""

from argparse import ArgumentParser
import sys
import re
import os

VALID_TYPES = [
    "feat",
    "fix",
    "build",
    "docs",
    "perf",
    "refactor",
    "revert",
    "style",
    "test",
    "chore"
]

#
# Maximum depth that scope directory can be. Indexed from 0.
#
SCOPE_MAX_DEPTH = 1

msg_has_trailer = False

def print_valid_types():
    for t in VALID_TYPES:
        print("- " + t)

    print()

#
# Print total number of errors and warnings, and exit with error code.
#
def print_stats_and_exit(total_errors, total_warnings):
    print("\ntotal: " + str(total_errors) + " errors, " +
          str(total_warnings) + " warnings")

    if total_errors:
        sys.exit(1)
    else:
        sys.exit(0)

#
# Return a list of directories up to a specified depth. These directories are
# valid scopes.
#
def get_valid_dirs(project_root):
    valid_directories = []

    #
    # Iterate through all subdirectories, include only the ones which are at or
    # below the maximum depth.
    #
    for directory,_,_ in os.walk(project_root):
        relative_dir = os.path.relpath(directory, project_root)
        if str(relative_dir).count(os.path.sep) <= SCOPE_MAX_DEPTH:
            valid_directories.append(str(relative_dir))

    return valid_directories

def check_title(title, project_root):
    errors = 0
    warnings = 0

    if not title:
        print("Commit message: ERROR: Title cannot be empty")
        errors += 1
        return errors, warnings

    if len(title) > 72:
        print("Commit message: ERROR: Title must be 72 characters or less")
        errors += 1

    title_parts = title.split(": ", 1)

    if len(title_parts) < 2:
        print("Commit message: ERROR: Title should be of the form:\n\ttype(scope): description\n")
        errors += 1
        return errors, warnings

    title_type_scope = title_parts[0]

    if not title_type_scope.islower():
        print("Commit message: ERROR: Subject type must be lowercase")
        errors += 1

    #
    # Extract the type and scope from the subject
    #
    scope_match = re.search(r"\(.*\)", title_type_scope)

    if scope_match is None:
        scope = ""
        title_type = title_type_scope
    else:
        scope = scope_match.group().strip("()")
        scope_begin_index = scope_match.span()[0]
        title_type = title_type_scope[:scope_begin_index]

    if not title_type in VALID_TYPES:
        print("Commit message: ERROR: Subject type must be one of the following:")
        print_valid_types()
        errors += 1

    if scope:
        valid_scopes = get_valid_dirs(project_root)
        if scope not in valid_scopes:
            print("Commit message: WARNING: Scope should match the directory where the patch applies")
            warnings += 1
    else:
        print("Commit message: WARNING: Consider adding a scope to the subject")
        warnings += 1

    description = title_parts[1].lstrip()
    if not description:
        print("Commit message: ERROR: Title description cannot be empty")
        errors += 1

    return errors, warnings

def check_body(lines):
    errors = 0
    warnings = 0

    nonempty_lines = [l for l in lines if l != ""]

    #
    # Check if commit message body is empty
    #
    if (not lines or not nonempty_lines):
        print("Commit message: WARNING: Consider adding a commit message body")
        warnings += 1
        return errors, warnings

    #
    # Verify that at least one empty line separates the title from the body and
    # the body from the trailer
    #
    if lines[0] != "":
        print("Commit message: ERROR: Empty line required between title and body")
        errors += 1

    if lines[-1] != "":
        print("Commit message: ERROR: Empty line required between body and trailer")
        errors += 1

    #
    # Verify that the width of the commit message body is 72 chars or less
    #
    for line in nonempty_lines:
        if len(line) > 72:
            print("Commit message: ERROR: Width of commit message body must be 72 characters or less")
            errors += 1
            return errors, warnings

    return errors, warnings

#
# Check that the trailer contains both a Signed-off-by and Change-Id.
#
def check_trailer(trailer_lines):
    has_signed_off_by = False
    has_change_id = False

    num_change_id = 0

    errors = 0
    warnings = 0

    for line in trailer_lines:
        signed_off_by_match = re.search("^Signed-off-by: .* <.*>$", line)
        if signed_off_by_match is not None:
            has_signed_off_by = True

        change_id_match = re.search("^Change-Id: I.*", line)
        if change_id_match is not None:
            has_change_id = True
            num_change_id += 1

    if not has_signed_off_by:
        print("Commit message: ERROR: Trailer must contain Signed-off-by")
        errors += 1

    if (not has_change_id or num_change_id > 1):
        print("Commit message: ERROR: Trailer must contain exactly one Change-Id")
        errors += 1

    return errors, warnings

#
# Verify if the "trailer" discovered by find_trailer() is actually a trailer. It
# is assumed that if the discovered "trailer" doesn't have a Signed-off-by or
# Change-Id, it is actually just part of the commit message body and the
# message doesn't include a trailer.
#
def verify_if_trailer(lines):
    for line in lines:
        signed_off_by_match = re.search("^Signed-off-by: .* <.*>$", line)
        if signed_off_by_match is not None:
            return True

        change_id_match = re.search("^Change-Id: I.*", line)
        if change_id_match is not None:
            return True

    return False

#
# Try to find a trailer in the commit message by finding the final "block" of
# the message. Note that this may not actually be a trailer - this is verified
# later in the script. Returns the index of the line that this final "block"
# begins on.
#
def find_trailer(message_lines):
    #
    # Iterate backwards over the message, starting at the last line. Stop when
    # an empty line is encountered, signalling the start of the block.
    #
    for idx, line in reversed(list(enumerate(message_lines))):
        if line == "":
            return idx + 1

    return 0

#
# Remove any trailing newlines at the end of the commit message
#
def remove_trailing_newlines(message_lines):
    while message_lines[-1] == "":
        message_lines.pop(-1)

def check_commit_msg(message, project_root):
    total_errors = 0
    total_warnings = 0

    #
    # Convert message into a list of its lines, and remove trailing empty lines
    #
    message_lines = message.splitlines()

    remove_trailing_newlines(message_lines)

    if not message_lines:
        print("Commit message: ERROR: Commit message cannot be empty")
        total_errors += 1

    trailer_start_idx = find_trailer(message_lines)

    msg_has_trailer = verify_if_trailer(message_lines[trailer_start_idx:])

    if msg_has_trailer:
        trailer = message_lines[trailer_start_idx:]

        if trailer_start_idx == 0:
            print("Commit message: ERROR: Commit message must have at least a title")
            total_errors += 1

            title = ""
            body = []
        elif trailer_start_idx == 1:
            title = message_lines[0]
            body = []
        else:
            title = message_lines[0]
            body = message_lines[1:trailer_start_idx]
    else:
        print("Commit message: ERROR: Commit message must contain a trailer with Signed-off-by and Change-Id")
        total_errors += 1

        title = message_lines[0]
        body = message_lines[1:]

    title_errors, title_warnings = check_title(title, project_root)
    body_errors, body_warnings = check_body(body)

    total_errors += title_errors + body_errors
    total_warnings += title_warnings + body_warnings

    if msg_has_trailer:
        trailer_errors, trailer_warnings = check_trailer(trailer)

        total_errors += trailer_errors
        total_warnings += trailer_warnings

    return total_errors, total_warnings

def main():
    parser = ArgumentParser(description='Check commit messages')
    parser.add_argument('--project-root', type=str, required=True)
    parser.add_argument('message')

    args = parser.parse_args()

    total_errors, total_warnings = check_commit_msg(args.message,
                                                    args.project_root)
    print_stats_and_exit(total_errors, total_warnings)

if __name__ == '__main__':
    main()

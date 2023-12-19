#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

"""
This script is used to compare the summary of the CBMC analysis with the
baseline. The script prints an error message and returns error code if there is
a parsing error, or the change in the summary is not compatible with the baseline.
In the latter case, either the baseline should be updated, or the RMM code or the
CBMC testbench needs to be fixed.

The script assumes that the summary lines of the `analysis` and the `assert` modes
have the same format and semantics
"""

import argparse
import logging
import ntpath
import re
import sys


class ParseException(Exception):
    """
    An exception of this type is raised in case of parsing error
    """


class CompareException(Exception):
    """
    An exception of this type is raised when there is a difference in the
    summaries that should be fixed.
    """


re_summary_prefix = re.compile(r"\|\s*([a-z_.]+)\s*\|\s*(\d+)\s+of\s+(\d+)")
re_separator = re.compile(r"\+-+\+-+\+")
re_header = re.compile(r"\|\s*[A-Z_]+\s*\|\s*([A-Z_]+)\s*\|")
re_failed_analysis = re.compile(r"\|\s*([a-z_.]+)\s*\|\s*N\/A\s*\|")


def parse_summary_file(summary_file_name):
    """
    Parse a single summary file.

    Returns a tuple:
    (summary type as a string, list of summaries)

    Each element in the list of summaries is a tuple of three values:
    (testbench name, first integer value, second integer value)
    """
    logging.debug(f"Parsing file {summary_file_name}")
    with open(summary_file_name, "r", encoding="utf-8") as file:
        lines = file.readlines()

    summary_type = None
    summary_list = []

    for idx, line in enumerate(lines):
        line = line.strip()
        if not line:
            continue
        m_separator = re_separator.match(line)
        if m_separator:
            continue
        m_summary_prefix = re_summary_prefix.match(line)
        if m_summary_prefix:
            logging.debug(f"    summary line '{line}'")
            if not summary_type:
                raise ParseException(
                    f"Missing summary header in file {summary_file_name}"
                )
            summary_list.append(
                (
                    m_summary_prefix.group(1),
                    int(m_summary_prefix.group(2)),
                    int(m_summary_prefix.group(3)),
                )
            )
            continue
        m_header = re_header.match(line)
        if m_header:
            summary_type = m_header.group(1)
            logging.debug(f"    header line '{line}'")
            continue
        m_failed_analysis = re_failed_analysis.match(line)
        if m_failed_analysis:
            logging.debug(f"    N/A line '{line}'")
            raise ParseException(
                f"CBMC Analysis failed in {summary_file_name} for {m_failed_analysis.group(1)} "
                + "Please fix RMM/testbench code"
            )
        logging.debug(f"    Parse failed on line '{line}'")
        raise ParseException(f"Invalid line in {summary_file_name} at line {idx+1}")

    if not summary_list:
        raise ParseException(f"No summary in file {summary_file_name}")

    logging.info(f"Summary type of {summary_file_name} is {summary_type}")

    return summary_type, summary_list


def compare_coverage_summary(testbench_name, baseline_results, current_results):
    """
    Compare two coverage summary lines.

    The results must be in the form of tuple:
    (first integer value, second integer value)
    """
    logging.debug(
        f"Comparing {baseline_results[0]} of {baseline_results[1]} against "
        + f"{current_results[0]} of {current_results[1]}"
    )
    if baseline_results[0] < current_results[0]:
        raise CompareException(
            f"The coverage of {testbench_name} increased "
            + f"({baseline_results[0]}->{current_results[0]}). "
            + "Please update the baseline for later checks."
        )
    if baseline_results[0] > current_results[0]:
        raise CompareException(
            f"The coverage of {testbench_name} decreased "
            + f"({baseline_results[0]}->{current_results[0]}). "
            + "Please update the baseline if this is acceptable."
        )
    if baseline_results[1] != current_results[1]:
        logging.warning(
            f"The number of coverage tests in {testbench_name} changed. "
            + f"({baseline_results[1]}->{current_results[1]}). "
            + "Please consider updating the baseline."
        )


def compare_assert_summary(testbench_name, baseline_results, current_results):
    """
    Compare two assert summary lines.

    The results must be in the form of tuple:
    (first integer value, second integer value)
    """
    logging.debug(
        f"Comparing {baseline_results[0]} of {baseline_results[1]} against "
        + f"{current_results[0]} of {current_results[1]}"
    )
    if baseline_results[0] < current_results[0]:
        raise CompareException(
            f"The number of failed asserts in {testbench_name} increased "
            + f"({baseline_results[0]}->{current_results[0]}). "
            + "Please update the baseline if this is acceptable."
        )
    if baseline_results[0] > current_results[0]:
        raise CompareException(
            f"The number of failed asserts in {testbench_name} decreased "
            + f"({baseline_results[0]}->{current_results[0]}). "
            + "Please update the baseline for later checks."
        )
    # The number of asserts in the code can change frequently, so don't do a check on it.


def compare_summary_lists(baseline_list, actual_list, comparator, testbench_list):
    """
    Compare two summary lists.

    Arguments:
    baseline_list -- List of testbench baseline results
    actual_list -- List of testbench actual results
    comparator -- A function that can compare 2 testbench result items
    testbench_list -- A list of testbenches to be considered. If None, all
                      testbenches are considered

    baseline_list and  actual_list items are expected to be in the format of a
    tuple: (testbench name, first integer value, second integer value)

    """
    # TODO: check for duplicated lines
    baseline = {summary[0]: summary[1:] for summary in baseline_list}

    # It is important to first check the common lines, and only report any
    # missing or extra testbenches after that. This is to make sure that no
    # coverage/assert change remains unnoticed due to an update of the baseline
    # that was triggered by a tetsbench addition/deletion.
    actual_extra = {}

    if testbench_list is not None:
        baseline = {k: v for k, v in baseline.items() if k in testbench_list}
        actual_list = [e for e in actual_list if e[0] in testbench_list]

    for summary in actual_list:
        testbench_name = summary[0]
        if testbench_name not in baseline.keys():
            actual_extra[testbench_name] = summary[1:]
            continue
        comparator(testbench_name, baseline[testbench_name], summary[1:])
        del baseline[testbench_name]
    if baseline:
        raise CompareException(
            f"{next(iter(baseline))} is missing from the actual result. Please update baseline!"
        )
    if actual_extra:
        raise CompareException(
            f"{testbench_name} is missing from the baseline. Please update baseline!"
        )


def compare_summary_files(baseline_filename, actual_filename, testbench_list):
    """
    Compare two summary files.
    """
    base_type, base_summary_list = parse_summary_file(baseline_filename)
    actual_type, actual_summary_list = parse_summary_file(actual_filename)

    if base_type != actual_type:
        raise ParseException(
            f"{baseline_filename} and {actual_filename} have different summary type"
        )

    comparators = {
        "COVERAGE": compare_coverage_summary,
        "ANALYSIS": compare_assert_summary,
        "ASSERT": compare_assert_summary,
    }

    if base_type not in comparators:
        raise ParseException(f"Unknown summary type {base_type}")

    compare_summary_lists(
        base_summary_list, actual_summary_list, comparators[base_type], testbench_list
    )


def main():
    """
    main function of the script.
    """
    parser = argparse.ArgumentParser(description="compare CBMC summary siles")
    parser.add_argument(
        "--testbench-files",
        type=str,
        help="A semicolon (;) separated list of files to check in the summaries.",
    )
    parser.add_argument(
        "baseline",
        type=str,
        help="The path of the baseline summary file.",
    )
    parser.add_argument(
        "actual", type=str, help="The path of the current summary file."
    )
    args = parser.parse_args()

    if args.testbench_files:
        testbench_list = [ntpath.basename(p) for p in args.testbench_files.split(";")]
    else:
        testbench_list = None

    try:
        compare_summary_files(args.baseline, args.actual, testbench_list)
    except ParseException as exc:
        logging.error("Failed to compare summaries:")
        logging.error(f"{str(exc)}")
        sys.exit(1)
    except CompareException as exc:
        logging.error("The results contain significant differences:")
        logging.error(f"{str(exc)}")
        sys.exit(1)


if __name__ == "__main__":
    logging.basicConfig(format="%(message)s", level=logging.WARNING)
    main()

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>
#include <test_groups.h>

int main(int argc, char **argv)
{
	return CommandLineTestRunner::RunAllTests(argc, argv);
}

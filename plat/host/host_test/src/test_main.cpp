/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <app.h>
#include <host_utils.h>
}

#include <test_groups.h>

/*
 * Register the host app executables before tests can boot RMM. Reap the app
 * processes after the suite and return the CppUTest result unchanged.
 */
int main(int argc, char **argv)
{
	int result;

	host_util_initialise_app_headers(argc, argv);
	result = CommandLineTestRunner::RunAllTests(argc, argv);
	app_processes_cleanup();

	return result;
}

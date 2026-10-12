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

extern "C" {
#include <test_helpers.h>
}

/*
 * Register the host app executables and runner path before tests can boot RMM.
 * Stop any remaining responder, reap app processes, and preserve the test result.
 */
int main(int argc, char **argv)
{
	int result;

	host_util_initialise_app_headers(argc, argv);
	test_helpers_set_executable_path(argv[0]);
	result = CommandLineTestRunner::RunAllTests(argc, argv);
	host_util_stop_spdm_responder();
	app_processes_cleanup();

	return result;
}

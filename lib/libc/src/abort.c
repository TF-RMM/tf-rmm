/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <debug.h>

void abort(void)
{
	ERROR("ABORT\n");
	panic();
}

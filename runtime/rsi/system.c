/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#include <assert.h>
#include <smc-rsi.h>

COMPILER_ASSERT(RSI_ABI_VERSION_MAJOR <= 0x7FFF);
COMPILER_ASSERT(RSI_ABI_VERSION_MINOR <= 0xFFFF);

unsigned long handle_rsi_version(void)
{
	return RSI_ABI_VERSION;
}

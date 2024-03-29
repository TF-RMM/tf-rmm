/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 790fd539
 */

#ifndef __TB_RMI_VERSION_H
#define __TB_RMI_VERSION_H

#include "stdbool.h"
#include "stdint.h"

/*
 * Testbench for RMI_VERSION command. Check via CBMC with flag
 * `--entry-point tb_rmi_version`.
 *
 * Arguments:
 *     req: Requested interface revision.
 *
 * Returns:
 *     bool: Output value.
 */
bool tb_rmi_version(
	rmi_interface_version_t req);

#endif /* __TB_RMI_VERSION_H */

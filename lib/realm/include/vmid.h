/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef VMID_H
#define VMID_H

#include <stdbool.h>

bool vmid_reserve(unsigned int vmid);
void vmid_free(unsigned int vmid);

#endif /* VMID_H */

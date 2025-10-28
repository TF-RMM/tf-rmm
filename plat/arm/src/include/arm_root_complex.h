/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ARM_ROOT_COMPLEX_H
#define ARM_ROOT_COMPLEX_H

#include <rmm_el3_ifc.h>
#include <stddef.h>
#include <stdint.h>

void arm_set_root_complex_list(struct root_complex_list *rc_list);

#endif /* ARM_ROOT_COMPLEX_H */

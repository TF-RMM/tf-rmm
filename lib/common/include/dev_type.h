/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef DEV_TYPE_H
#define DEV_TYPE_H

/* Types of device memory */
enum dev_type {
	DEV_RANGE_COHERENT,
	DEV_RANGE_NON_COHERENT,
	DEV_RANGE_MAX
};

#endif /* DEV_TYPE_H */

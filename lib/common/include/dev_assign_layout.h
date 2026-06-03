/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef DEV_ASSIGN_LAYOUT_H
#define DEV_ASSIGN_LAYOUT_H

#include <utils_def.h>

/*
 * Maximum vdevs_order supported by the implementation.
 */
#ifndef CBMC
#define MAX_VDEVS_ORDER				UL(10)
/*
 * Sized to cover the stream page, the VDEV range pages needed for
 * MAX_VDEVS_ORDER, and the current device-assignment app requirement.
 */
#define MAX_PDEV_PARAM_AUX_GRANULES		U(72)
#define MAX_PDEV_APP_AUX_GRANULES		U(34)
#else /* CBMC */
#define MAX_VDEVS_ORDER				UL(2)
#define MAX_PDEV_PARAM_AUX_GRANULES		U(3)
#define MAX_PDEV_APP_AUX_GRANULES		U(1)
#endif /* CBMC */

#endif /* DEV_ASSIGN_LAYOUT_H */

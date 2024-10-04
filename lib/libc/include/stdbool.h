/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef STDBOOL_H
#define STDBOOL_H

#define bool	_Bool

#define true	(bool)(0 < 1)
#define false	(bool)(0 > 1)

/* Signal that all the definitions are present.  */
#define __bool_true_false_are_defined	1

#endif /* STDBOOL_H */

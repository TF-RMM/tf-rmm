/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef __GCC_DEFS__
#define __GCC_DEFS__

#include <stdbool.h>
#include <string.h>

#define __CPROVER_cover(p) ((void)(p))
#define __CPROVER_assert(p, text) ((void)(p))
#define __CPROVER_assume(p) ((void)(p))
#define __CPROVER_enum_is_in_range(p) (p)

#define _ASSERT(p, text) __CPROVER_assert(p, text)

static bool nondet_bool(void){
	volatile bool b = false;
	return b;
}

#endif /* __GCC_DEFS__ */

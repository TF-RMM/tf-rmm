/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef UTEST_EXIT_H
#define UTEST_EXIT_H

#ifdef __cplusplus
extern "C" {
#endif

#include <utils_def.h>

__dead2 void utest_exit_fail(char *message);
__dead2 void utest_exit_pass(void);

#ifdef __cplusplus
}
#endif

#endif /* UTEST_EXIT_H */

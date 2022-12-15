/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#ifndef PAUTH_PVT_H
#define PAUTH_PVT_H

/* Use this attribute to disable PAuth for a function. */
#define PAUTH_NONE_ATTR __attribute__((target("branch-protection=none")))

#endif /* PAUTH_PVT_H */

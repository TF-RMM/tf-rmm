/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RSI_RDEV_CALL_H
#define RSI_RDEV_CALL_H

struct rec;

/* Complete the vdev_communicate flow when REC_ENTER is called. */
void handle_rsi_rdev_complete(struct rec *rec);

#endif /* RSI_RDEV_CALL_H */

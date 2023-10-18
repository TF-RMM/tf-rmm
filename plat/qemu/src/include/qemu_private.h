/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef QEMU_PRIVATE_H
#define QEMU_PRIVATE_H

/*
 * QEMU doesn't emulate the clock or baudrate, so these are arbitrary.
 * The virt platform advertises a 24MHz clock to make Linux probe work.
 */
#define QEMU_UART_BAUDRATE		115200
#define QEMU_UART_CLK_IN_HZ		24000000

#endif /* QEMU_PRIVATE_H */

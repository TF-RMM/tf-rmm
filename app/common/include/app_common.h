/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef APP_COMMON_H
#define APP_COMMON_H

#ifndef __ASSEMBLER__
#include <stddef.h>
#include <stdint.h>
#endif /* __ASSEMBLER__ */
#include <utils_def.h>

/* The heap properties are encoded in a single unsigned long.
 * It is assumed that the heap_va is granule aligned, so at
 * least the lower 12 bits are always zero.
 */
#define HEAP_PAGE_COUNT_MASK ((1UL << 12U) - 1UL)
#define HEAP_VA_MASK (~HEAP_PAGE_COUNT_MASK)

#define APP_EXIT_CALL		UL(23)
#define APP_SERVICE_CALL	UL(47)

#define APP_SERVICE_COUNT			16U
#define APP_SERVICE_PRINT			2U

#endif /* APP_COMMON_H */

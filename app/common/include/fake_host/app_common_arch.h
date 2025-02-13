/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef APP_COMMON_ARCH_H
#define APP_COMMON_ARCH_H

#define CREATE_NEW_APP_INSTANCE		13
#define CALL_APP_INSTANCE		21

#define OP_OR_EXIT(op, fd, buf, count, error_on_eof)                                               \
	do {                                                                                       \
		size_t count_processed = 0;                                                        \
		size_t op_or_exit_ret;                                                             \
		while (1) {                                                                        \
			op_or_exit_ret = op(fd, &((char *)buf)[count_processed],                   \
					    count - count_processed);                              \
			if (op_or_exit_ret > 0) {                                                  \
				count_processed += op_or_exit_ret;                                 \
				if (count_processed == count) {                                    \
					break;                                                     \
				}                                                                  \
			} else {                                                                   \
				if (error_on_eof) {                                                \
					ERROR("ERROR: Failed to " #op " %lu bytes at %s:%d\n"      \
						, count, __func__, __LINE__);                      \
					exit(1);                                                   \
				} else {                                                           \
					exit(0);                                                   \
				}                                                                  \
			}                                                                          \
		}                                                                                  \
	} while (0)

#define READ_OR_EXIT_NOERROR(fd, buf, count) OP_OR_EXIT(read, fd, buf, count, false)
#define READ_OR_EXIT(fd, buf, count) OP_OR_EXIT(read, fd, buf, count, true)
#define WRITE_OR_EXIT(fd, buf, count) OP_OR_EXIT(write, fd, buf, count, true)

#endif /* APP_COMMON_ARCH_H */

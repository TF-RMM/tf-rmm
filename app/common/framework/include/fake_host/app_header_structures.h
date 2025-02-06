/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef APP_HEADER_STRUCTURES_H
#define APP_HEADER_STRUCTURES_H

struct app_header {
	unsigned long app_id;
	char *app_elf_name;
};

#endif /* APP_HEADER_STRUCTURES_H */

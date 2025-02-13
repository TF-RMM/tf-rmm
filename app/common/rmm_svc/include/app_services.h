/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_fw_structures.h>

#ifndef APP_SERVICES_H
#define APP_SERVICES_H

/* Services management */
uint64_t call_app_service(unsigned long service_id,
			  struct app_data_cfg *app_data,
			  unsigned long arg0,
			  unsigned long arg1,
			  unsigned long arg2,
			  unsigned long arg3);

#endif /* APP_SERVICES_H */

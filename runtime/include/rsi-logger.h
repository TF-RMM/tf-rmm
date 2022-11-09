/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RSI_LOGGER_H
#define RSI_LOGGER_H

#include <debug.h>

/*
 * RSI_LOG_LEVEL debug level is set to one of:
 * LOG_LEVEL_NONE    = 0
 * LOG_LEVEL_ERROR   = 10
 * LOG_LEVEL_NOTICE  = 20
 * LOG_LEVEL_WARNING = 30
 * LOG_LEVEL_INFO    = 40
 * LOG_LEVEL_VERBOSE = 50
 */
#if (RSI_LOG_LEVEL >= LOG_LEVEL_ERROR) && (RSI_LOG_LEVEL <= LOG_LEVEL)

void rsi_log_on_exit(unsigned int function_id, unsigned long args[5],
		     unsigned long res, bool exit_to_rec);

/* Store SMC RSI parameters */
# define RSI_LOG_SET(x0, x1, x2, x3, x4)	\
	unsigned long rsi_log_args[5] = {x0, x1, x2, x3, x4}

/*
 * Macro prints RSI call function name, parameters
 * and result when returning back to REC
 */
# define RSI_LOG_EXIT(id, res, ret)	\
	rsi_log_on_exit(id, rsi_log_args, res, ret)

#else
# define RSI_LOG_SET(x0, x1, x2, x3, x4)
# define RSI_LOG_EXIT(id, res, ret)

#endif /* (>= LOG_LEVEL_ERROR) && (<= LOG_LEVEL) */
#endif /* RSI_LOGGER_H */

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
#if (RSI_LOG_LEVEL > LOG_LEVEL_NONE) && (RSI_LOG_LEVEL <= LOG_LEVEL)

void rsi_log_on_exit(unsigned int function_id, unsigned long args[],
		     unsigned long regs[]);

/*
 * Store SMC RSI parameters. Takes an array of regs[] of size
 * of at least 11 elements and sets up the args for RSI log.
 */
# define RSI_LOG_SET(regs)	\
	unsigned long rsi_log_args[] = {			\
		(regs)[1], (regs)[2], (regs)[3], (regs)[4], (regs)[5],	\
		(regs)[6], (regs)[7], (regs)[8], (regs)[9], (regs)[10]	\
	}

/*
 * Macro prints RSI call function name, parameters and result values
 */
# define RSI_LOG_EXIT(id, res)	rsi_log_on_exit(id, rsi_log_args, res)

#else
# define RSI_LOG_SET(regs)
# define RSI_LOG_EXIT(id, res)

#endif /* (> LOG_LEVEL_NONE) && (<= LOG_LEVEL) */
#endif /* RSI_LOGGER_H */

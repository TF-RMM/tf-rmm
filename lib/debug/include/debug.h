/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef DEBUG_H
#define DEBUG_H

#ifndef __ASSEMBLER__
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#endif
#include <utils_def.h>

/*
 * The log output macros print output to the console. These macros produce
 * compiled log output only if the LOG_LEVEL defined in the makefile (or the
 * make command line) is greater or equal than the level required for that
 * type of log output.
 *
 * The format expected is the same as for printf(). For example:
 * INFO("Info %s.\n", "message")    -> INFO:    Info message.
 * WARN("Warning %s.\n", "message") -> WARNING: Warning message.
 */
#define LOG_LEVEL_NONE		0
#define LOG_LEVEL_ERROR		10
#define LOG_LEVEL_NOTICE	20
#define LOG_LEVEL_WARNING	30
#define LOG_LEVEL_INFO		40
#define LOG_LEVEL_VERBOSE	50

/* If the LOG_LEVEL is not defined through the build */
#ifndef LOG_LEVEL
  #ifdef NDEBUG /* Release */
    #define LOG_LEVEL	LOG_LEVEL_NOTICE
  #else /* Debug */
    #define LOG_LEVEL	LOG_LEVEL_INFO
  #endif
#endif

#ifndef __ASSEMBLER__
/*
 * If the log output is too low then this macro is used in place of rmm_log()
 * below. The intent is to get the compiler to evaluate the function call for
 * type checking and format specifier correctness but let it optimize it out.
 */
#define no_rmm_log(fmt, ...)				\
	do {						\
		if (false) {				\
			rmm_log(fmt, ##__VA_ARGS__);	\
		}					\
	} while (false)

#if LOG_LEVEL >= LOG_LEVEL_ERROR
# define ERROR(...)	rmm_log(__VA_ARGS__)
#else
# define ERROR(...)	no_rmm_log(__VA_ARGS__)
#endif

#if LOG_LEVEL >= LOG_LEVEL_NOTICE
# define NOTICE(...)	rmm_log(__VA_ARGS__)
#else
# define NOTICE(...)	no_rmm_log(__VA_ARGS__)
#endif

#if LOG_LEVEL >= LOG_LEVEL_WARNING
# define WARN(...)	rmm_log(__VA_ARGS__)
#else
# define WARN(...)	no_rmm_log(__VA_ARGS__)
#endif

#if LOG_LEVEL >= LOG_LEVEL_INFO
# define INFO(...)	rmm_log(__VA_ARGS__)
#else
# define INFO(...)	no_rmm_log(__VA_ARGS__)
#endif

#if LOG_LEVEL >= LOG_LEVEL_VERBOSE
# define VERBOSE(...)	rmm_log(__VA_ARGS__)
#else
# define VERBOSE(...)	no_rmm_log(__VA_ARGS__)
#endif

/*
 * FIXME: Fully implement panic() handlers once it is decided how to panic.
 */

#define panic()				\
	do {				\
	} while (true)

__attribute__((__format__(__printf__, 1, 2)))
static inline void rmm_log(const char *fmt, ...)
{
	va_list args;

	va_start(args, fmt);
	(void)vprintf(fmt, args);
	va_end(args);
}

void backtrace(uintptr_t frame_pointer);

#endif /* __ASSEMBLER__ */
#endif /* DEBUG_H */

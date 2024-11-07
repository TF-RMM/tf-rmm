/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <psci.h>
#include <rsi-logger.h>
#include <smc-rsi.h>
#include <string.h>
#include <utils_def.h>

/* RMI handler uses 29 chars for function name */
#define MAX_NAME_LEN	29UL

/* Max 10 64-bit parameters separated by space */
#define PARAMS_STR_LEN	(10UL * sizeof("0123456789ABCDEF"))

#define MAX_STATUS_LEN	sizeof("RSI_ERROR_UNKNOWN")

#define BUFFER_SIZE	(MAX_NAME_LEN + PARAMS_STR_LEN + \
			sizeof(" > ") - 1UL + MAX_STATUS_LEN)

#define WHITESPACE_CHAR	0x20

struct rsi_handler {
	const char *fn_name;	/* function name */
	unsigned int num_args;	/* number of arguments */
	unsigned int num_vals;	/* number of output values */
};

#define RSI_HANDLER_ID(_id)	SMC64_FID_OFFSET_FROM_RANGE_MIN(RSI, SMC_RSI##_id)

#define RSI_FUNCTION(_id, _in, _out)[RSI_HANDLER_ID(_id)] = { \
	.fn_name = (#_id),	\
	.num_args = (_in),	\
	.num_vals = (_out)	\
}

static const struct rsi_handler rsi_logger[] = {
	RSI_FUNCTION(_VERSION, 1U, 2U),			/* 0xC4000190 */
	RSI_FUNCTION(_FEATURES, 1U, 1U),		/* 0xC4000191 */
	RSI_FUNCTION(_MEASUREMENT_READ, 1U, 8U),	/* 0xC4000192 */
	RSI_FUNCTION(_MEASUREMENT_EXTEND, 10U, 0U),	/* 0xC4000193 */
	RSI_FUNCTION(_ATTEST_TOKEN_INIT, 8U, 1U),	/* 0xC4000194 */
	RSI_FUNCTION(_ATTEST_TOKEN_CONTINUE, 3U, 1U),	/* 0xC4000195 */
	RSI_FUNCTION(_REALM_CONFIG, 1U, 0U),		/* 0xC4000196 */
	RSI_FUNCTION(_IPA_STATE_SET, 4U, 2U),		/* 0xC4000197 */
	RSI_FUNCTION(_IPA_STATE_GET, 2U, 2U),		/* 0xC4000198 */
	RSI_FUNCTION(_HOST_CALL, 1U, 0U),		/* 0xC4000199 */
	RSI_FUNCTION(_MEM_GET_PERM_VALUE, 2U, 1U),	/* 0xC40001A0 */
	RSI_FUNCTION(_MEM_SET_PERM_INDEX, 4U, 3U),	/* 0xC40001A1 */
	RSI_FUNCTION(_MEM_SET_PERM_VALUE, 3U, 0U),	/* 0xC40001A2 */
	RSI_FUNCTION(_PLANE_ENTER, 2U, 0U),		/* 0xC40001A3 */
	RSI_FUNCTION(_RDEV_CONTINUE, 2U, 0U),		/* 0xC40001A4 */
	RSI_FUNCTION(_RDEV_GET_INFO, 2U, 0U),		/* 0xC40001A5 */
	RSI_FUNCTION(_RDEV_GET_INTERFACE_REPORT, 3U, 1U),	/* 0xC40001A6 */
	RSI_FUNCTION(_RDEV_GET_MEASUREMENTS, 3U, 0U),	/* 0xC40001A7 */
	RSI_FUNCTION(_RDEV_GET_STATE, 2U, 1U),		/* 0xC40001A8 */
	RSI_FUNCTION(_RDEV_LOCK, 2U, 0U),		/* 0xC40001A9 */
	RSI_FUNCTION(_RDEV_START, 2U, 0U),		/* 0xC40001AA */
	RSI_FUNCTION(_RDEV_STOP, 2U, 0U),		/* 0xC40001AB */
	RSI_FUNCTION(_RDEV_VALIDATE_MAPPING, 6U, 2U),	/* 0xC40001AC */
	RSI_FUNCTION(_PLANE_REG_READ, 2U, 1U),		/* 0xC40001AE */
	RSI_FUNCTION(_PLANE_REG_WRITE, 3U, 0U)		/* 0xC40001AF */
};

#define RSI_STATUS_STRING(_id)[RSI_##_id] = #_id

static const char * const rsi_status_string[] = {
	RSI_STATUS_STRING(SUCCESS),
	RSI_STATUS_STRING(ERROR_INPUT),
	RSI_STATUS_STRING(ERROR_STATE),
	RSI_STATUS_STRING(INCOMPLETE),
	RSI_STATUS_STRING(ERROR_UNKNOWN),
	RSI_STATUS_STRING(ERROR_DEVICE)
};

COMPILER_ASSERT(ARRAY_SIZE(rsi_status_string) == RSI_ERROR_COUNT_MAX);

static const struct rsi_handler *fid_to_rsi_logger(unsigned int id)
{
	return &rsi_logger[id - SMC_RSI_VERSION];
}

static size_t print_entry(unsigned int id, unsigned long args[],
			  char *buf, size_t len)
{
	unsigned int num = 7U;	/* up to seven arguments */
	int cnt;

	switch (id) {
	case SMC_RSI_VERSION ... SMC_RSI_PLANE_REG_WRITE: {
		const struct rsi_handler *logger = fid_to_rsi_logger(id);

		num = logger->num_args;
		if (logger->fn_name != NULL) {
			cnt = snprintf(buf, MAX_NAME_LEN + 1UL,
				       "%s%s", "SMC_RSI", logger->fn_name);
		} else {
			cnt = snprintf(buf, MAX_NAME_LEN + 1UL,
				       "%s", "SMC_RSI_<unsupported>");
		}
		break;
	}
	/* SMC32 PSCI calls */
	case SMC32_PSCI_FID_MIN ... SMC32_PSCI_FID_MAX:
		FALLTHROUGH;
	case SMC64_PSCI_FID_MIN ... SMC64_PSCI_FID_MAX:
		cnt = snprintf(buf, MAX_NAME_LEN + 1UL, "%s%08x", "PSCI_", id);
		break;

	/* Other SMC calls */
	default:
		cnt = snprintf(buf, MAX_NAME_LEN + 1UL, "%s%08x", "SMC_", id);
		break;
	}

	assert((cnt > 0) && ((unsigned int)cnt < (MAX_NAME_LEN + 1U)));

	(void)memset((void *)((uintptr_t)buf + (unsigned int)cnt), WHITESPACE_CHAR,
					MAX_NAME_LEN - (size_t)cnt);

	buf = (char *)((uintptr_t)buf + MAX_NAME_LEN);
	len -= MAX_NAME_LEN;

	/* Arguments */
	for (unsigned int i = 0U; i < num; i++) {
		cnt = snprintf(buf, len, " %lx", args[i]);
		assert((cnt > 0) && (cnt < (int)len));
		buf = (char *)((uintptr_t)buf + (unsigned int)cnt);
		len -= (size_t)cnt;
	}

	return len;
}

static int print_status(char *buf, size_t len, unsigned long res)
{
	return_code_t rc = unpack_return_code(res);

	if ((unsigned long)rc.status >= RSI_ERROR_COUNT_MAX) {
		return snprintf(buf, len, " > %lx", res);
	}

	return snprintf(buf, len, " > RSI_%s",
			rsi_status_string[rc.status]);
}

static int print_code(char *buf, size_t len, unsigned long res)
{
	return snprintf(buf, len, " > %lx", res);
}

/* cppcheck-suppress misra-c2012-8.4 */
void rsi_log_on_exit(unsigned int function_id, unsigned long args[],
		     unsigned long regs[])
{
	char buffer[BUFFER_SIZE];
	size_t len = print_entry(function_id, args, buffer, sizeof(buffer));
	char *buf = (char *)((uintptr_t)buffer + sizeof(buffer) - len);
	unsigned int num = 3U;	/* results in X1-X3 */
	int cnt;

	switch (function_id) {
	case SMC_RSI_VERSION ... SMC_RSI_PLANE_REG_WRITE: {
		const struct rsi_handler *logger =
				fid_to_rsi_logger(function_id);

		/* Print status */
		cnt = print_status(buf, len, regs[0]);
		num = logger->num_vals;
		break;
	}
	default:
		/* Print result code */
		cnt = print_code(buf, len, regs[0]);
	}

	assert((cnt > 0) && (cnt < (int)len));

	/* Print output values */
	for (unsigned int i = 1U; i <= num; i++) {
		buf = (char *)((uintptr_t)buf + (unsigned int)cnt);
		len -= (size_t)cnt;
		cnt = snprintf(buf, len, " %lx", regs[i]);
		assert((cnt > 0) && (cnt < (int)len));
	}

	rmm_log("%s\n", buffer);
}

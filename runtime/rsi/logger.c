/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <psci.h>
#include <rsi-logger.h>
#include <smc-rsi.h>
#include <utils_def.h>

/* RMI handler uses 29 chars for function name */
#define	MAX_NAME_LEN	29U

/* 5 64-bit parameters separated by space + 1 trailing space */
#define PARAMS_STR_LEN	(5U * sizeof("0123456789ABCDEF") + 1U)

#define	MAX_STATUS_LEN	sizeof("{RSI_ERROR_INPUT}")

#define	BUFFER_SIZE	(MAX_NAME_LEN + PARAMS_STR_LEN +	\
			sizeof("> ") - 1U +		\
			MAX_STATUS_LEN)

#define RSI_FUNCTION(id) \
	[SMC_RSI_##id - SMC_RSI_ABI_VERSION] = #id

static const char *rsi_logger[] = {
	RSI_FUNCTION(ABI_VERSION),		/* 0xC4000190 */
	RSI_FUNCTION(MEASUREMENT_READ),		/* 0xC4000192 */
	RSI_FUNCTION(MEASUREMENT_EXTEND),	/* 0xC4000193 */
	RSI_FUNCTION(ATTEST_TOKEN_INIT),	/* 0xC4000194 */
	RSI_FUNCTION(ATTEST_TOKEN_CONTINUE),	/* 0xC4000195 */
	RSI_FUNCTION(REALM_CONFIG),		/* 0xC4000196 */
	RSI_FUNCTION(IPA_STATE_SET),		/* 0xC4000197 */
	RSI_FUNCTION(IPA_STATE_GET),		/* 0xC4000198 */
	RSI_FUNCTION(HOST_CALL)			/* 0xC4000199 */
};

#define RSI_STATUS_HANDLER(id)[id] = #id

const char *rsi_status_handler[] = {
	RSI_STATUS_HANDLER(RSI_SUCCESS),
	RSI_STATUS_HANDLER(RSI_ERROR_INPUT),
	RSI_STATUS_HANDLER(RSI_ERROR_STATE),
	RSI_STATUS_HANDLER(RSI_INCOMPLETE)
};

COMPILER_ASSERT(ARRAY_LEN(rsi_status_handler) == RSI_ERROR_COUNT);

static int print_entry(unsigned int id, unsigned long args[5],
		       char *buf, size_t len)
{
	char name[sizeof("SMC_RSI_ATTEST_TOKEN_CONTINUE")];
	int cnt __unused;

	switch (id) {
	case SMC_RSI_ABI_VERSION ... SMC_RSI_HOST_CALL:

		if (rsi_logger[id - SMC_RSI_ABI_VERSION] != NULL) {
			cnt = snprintf(name, sizeof(name), "%s%s", "SMC_RSI_",
			       rsi_logger[id - SMC_RSI_ABI_VERSION]);
		} else {
			/* Handle gaps in RSI commands numbering */
			cnt = snprintf(name, sizeof(name), "%s%08x", "SMC_RSI_", id);
		}

		break;

	/* SMC32 PSCI calls */
	case SMC32_PSCI_FID_MIN ... SMC32_PSCI_FID_MAX:
		FALLTHROUGH;
	case SMC64_PSCI_FID_MIN ... SMC64_PSCI_FID_MAX:
		cnt = snprintf(name, sizeof(name), "%s%08x", "PSCI_", id);
		break;

	/* Other SMC calls */
	default:
		cnt = snprintf(name, sizeof(name), "%s%08x", "SMC_", id);
		break;
	}

	assert((cnt > 0) && (cnt < sizeof(name)));

	return snprintf(buf, len, "%-29s %8lx %8lx %8lx %8lx %8lx ",
			name, args[0], args[1], args[2], args[3], args[4]);
}

static int print_status(char *buf, size_t len, unsigned long res)
{
	return_code_t rc = unpack_return_code(res);

	if ((unsigned long)rc.status >= RSI_ERROR_COUNT) {
		return snprintf(buf, len, "> %lx", res);
	}

	return snprintf(buf, len, "> %s",
			rsi_status_handler[rc.status]);
}

static int print_code(char *buf, size_t len, unsigned long res)
{
	return snprintf(buf, len, "> %lx", res);
}

void rsi_log_on_exit(unsigned int function_id, unsigned long args[5],
		     unsigned long res, bool exit_to_rec)
{
	char buffer[BUFFER_SIZE];
	char *buf_ptr = buffer;
	size_t buf_len = sizeof(buffer);
	int cnt = print_entry(function_id, args, buf_ptr, buf_len);

	assert((cnt > 0) && (cnt < buf_len));

	buf_ptr += cnt;
	buf_len -= cnt;

	/* Print result when execution continues in REC */
	if (exit_to_rec) {
		if ((function_id >= SMC_RSI_MEASUREMENT_READ) &&
		    (function_id <= SMC_RSI_HOST_CALL)) {
			/* Print status */
			cnt = print_status(buf_ptr, buf_len, res);
		} else {
			/* Print result code */
			cnt = print_code(buf_ptr, buf_len, res);
		}

		assert((cnt > 0) && (cnt < buf_len));
	}

	rmm_log("%s\n", buffer);
}

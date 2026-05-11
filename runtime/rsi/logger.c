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

/*
 * RSI handler uses 34 chars max for function name including the null
 * terminator
 */
#define MAX_NAME_LEN	sizeof("SMC_RSI_RDEV_GET_INTERFACE_REPORT")

/* Max 10 64-bit parameters separated by space */
#define PARAMS_STR_LEN	(10UL * sizeof("0123456789ABCDEF"))

#define MAX_STATUS_LEN	sizeof("RSI_ERROR_UNKNOWN")

#define BUFFER_SIZE	(MAX_NAME_LEN + PARAMS_STR_LEN + \
			sizeof(" > ") - 3UL + MAX_STATUS_LEN)

#define WHITESPACE_CHAR	0x20

struct rsi_handler {
	const char *fn_name;	/* function name */
	unsigned int num_args;	/* number of arguments */
	unsigned int num_vals;	/* number of output values */
	bool log_on_dispatch;	/* log when call exits without return status */
	bool log_on_success;	/* log when RSI_SUCCESS or RSI_INCOMPLETE */
	bool log_on_error;	/* log when error status */
};

#define RSI_HANDLER_ID(_id)	SMC64_FID_OFFSET_FROM_RANGE_MIN(RSI, SMC_RSI##_id)

#define RSI_FUNCTION(_id, _in, _out, _log_dispatch, _log_ok, _log_err) \
	[RSI_HANDLER_ID(_id)] = {		\
	.fn_name = (#_id),			\
	.num_args = (_in),			\
	.num_vals = (_out),			\
	.log_on_dispatch = (_log_dispatch),	\
	.log_on_success = (_log_ok),		\
	.log_on_error = (_log_err)		\
}

/*
 * Per-FID log control:
 * (id, in_args, out_vals, log_on_dispatch, log_on_success, log_on_error)
 * log_on_dispatch: log when call exits without a return status
 * log_on_success: log when call returns RSI_SUCCESS or RSI_INCOMPLETE
 * log_on_error:   log when call returns an error status
 * Default: log_on_dispatch=true, log_on_success=false, log_on_error=true
 */
static const struct rsi_handler rsi_logger[] = {
	RSI_FUNCTION(_VERSION,			1U,  2U, true,  true,  true),  /* 0xC4000190 */
	RSI_FUNCTION(_FEATURES,			1U,  1U, true,  true,  true),  /* 0xC4000191 */
	RSI_FUNCTION(_MEASUREMENT_READ,		1U,  8U, true,  false, true),  /* 0xC4000192 */
	RSI_FUNCTION(_MEASUREMENT_EXTEND,	10U, 0U, true,  false, true),  /* 0xC4000193 */
	RSI_FUNCTION(_ATTEST_TOKEN_INIT,	8U,  1U, true,  false, true),  /* 0xC4000194 */
	RSI_FUNCTION(_ATTEST_TOKEN_CONTINUE,	3U,  1U, false, false, true),  /* 0xC4000195 */
	RSI_FUNCTION(_REALM_CONFIG,		1U,  0U, true,  true,  true),  /* 0xC4000196 */
	RSI_FUNCTION(_IPA_STATE_SET,		4U,  2U, false, false, true),  /* 0xC4000197 */
	RSI_FUNCTION(_IPA_STATE_GET,		2U,  2U, true,  false, true),  /* 0xC4000198 */
	RSI_FUNCTION(_HOST_CALL,		1U,  0U, false, false, true),  /* 0xC4000199 */
	RSI_FUNCTION(_VDEV_DMA_ENABLE,		6U,  0U, false, false, true),  /* 0xC400019C */
	RSI_FUNCTION(_VDEV_GET_INFO,		2U,  0U, false, false, true),  /* 0xC400019D */
	RSI_FUNCTION(_VDEV_VALIDATE_MAPPING,	8U,  2U, false, false, true),  /* 0xC400019F */
	RSI_FUNCTION(_MEM_GET_PERM_VALUE,	2U,  1U, true,  false, true),  /* 0xC40001A0 */
	RSI_FUNCTION(_MEM_SET_PERM_INDEX,	4U,  3U, false, false, true),  /* 0xC40001A1 */
	RSI_FUNCTION(_MEM_SET_PERM_VALUE,	3U,  0U, true,  false, true),  /* 0xC40001A2 */
	RSI_FUNCTION(_PLANE_ENTER,		2U,  0U, false, false, true),  /* 0xC40001A3 */
	RSI_FUNCTION(_VDEV_DMA_DISABLE,		1U,  0U, false, false, true),  /* 0xC40001A4 */
	RSI_FUNCTION(_PLANE_SYSREG_READ,	2U,  1U, true,  false, true),  /* 0xC40001AE */
	RSI_FUNCTION(_PLANE_SYSREG_WRITE,	3U,  0U, true,  false, true)   /* 0xC40001AF */
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

/* cppcheck-suppress misra-c2012-17.3 */
COMPILER_ASSERT(ARRAY_SIZE(rsi_status_string) == RSI_ERROR_COUNT_MAX);

static const struct rsi_handler *fid_to_rsi_logger(unsigned int id)
{
	unsigned int offset = id - SMC_RSI_VERSION;

	return (offset < ARRAY_SIZE(rsi_logger)) ? &rsi_logger[offset] : NULL;
}

static size_t print_entry(unsigned int id, const struct rsi_handler *logger,
			  unsigned long args[],
			  char *buf, size_t len)
{
	unsigned int num = 7U;	/* up to seven arguments */
	int cnt;

	if (logger != NULL) {
		num = logger->num_args;
		if (logger->fn_name != NULL) {
			cnt = snprintf(buf, MAX_NAME_LEN,
				       "%s%s", "SMC_RSI", logger->fn_name);
		} else {
			cnt = snprintf(buf, MAX_NAME_LEN,
				       "%s", "SMC_RSI_<unsupported>");
		}
	} else {
		switch (id) {
		/* SMC32 PSCI calls */
		case SMC32_PSCI_FID_MIN ... SMC32_PSCI_FID_MAX:
			FALLTHROUGH;
		case SMC64_PSCI_FID_MIN ... SMC64_PSCI_FID_MAX:
			cnt = snprintf(buf, MAX_NAME_LEN, "%s%08x",
				       "PSCI_", id);
			break;

		/* Other SMC calls */
		default:
			cnt = snprintf(buf, MAX_NAME_LEN, "%s%08x", "SMC_", id);
			break;
		}
	}

	assert((cnt > 0) && ((unsigned int)cnt < MAX_NAME_LEN));

	(void)memset((void *)((uintptr_t)buf + (unsigned int)cnt), WHITESPACE_CHAR,
					MAX_NAME_LEN - (size_t)cnt);

	buf = (char *)((uintptr_t)buf + MAX_NAME_LEN - 1UL);
	len -= (MAX_NAME_LEN - 1UL);

	/* Keep zero-argument dispatch entries terminated after padding. */
	*buf = '\0';

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
/* cppcheck-suppress misra-c2012-8.7 */
void rsi_log_on_exit(unsigned int function_id, unsigned long args[],
		     unsigned long regs[], bool ret_to_rec)
{
	char buffer[BUFFER_SIZE];
	const struct rsi_handler *logger = fid_to_rsi_logger(function_id);
	size_t len;
	char *buf;
	unsigned int num;
	int cnt;
	bool is_non_error = false;

	/*
	 * Apply per-FID policy before formatting any arguments. Unsupported
	 * RSI and non-RSI calls are always logged. Dispatch-only exits have
	 * no return status, so do not inspect regs[] on that path.
	 */
	if ((logger != NULL) && (logger->fn_name != NULL)) {
		if (!ret_to_rec) {
			if (!logger->log_on_dispatch) {
				return;
			}
		} else {
			return_code_t rc = unpack_return_code(regs[0]);

			is_non_error = ((rc.status == RSI_SUCCESS) ||
					(rc.status == RSI_INCOMPLETE));

			if ((is_non_error && !logger->log_on_success) ||
			    (!is_non_error && !logger->log_on_error)) {
				return;
			}
		}
	}

	len = print_entry(function_id, logger, args, buffer, sizeof(buffer));
	buf = (char *)((uintptr_t)buffer + sizeof(buffer) - len);

	/*
	 * Return status and results in regs[] are only valid if the RSI call
	 * execution returns to REC.
	 */
	if (!ret_to_rec) {
		rmm_log("%s\n", buffer);
		return;
	}

	if (logger != NULL) {
		/* Print status */
		cnt = print_status(buf, len, regs[0]);
		num = is_non_error ? logger->num_vals : 0U;
	} else {
		/* Print result code */
		cnt = print_code(buf, len, regs[0]);
		num = 3U;	/* results in X1-X3 */
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

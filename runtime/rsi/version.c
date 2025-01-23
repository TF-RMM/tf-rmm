/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#include <assert.h>
#include <rec.h>
#include <rsi-handler.h>
#include <smc-rsi.h>
#include <stdbool.h>
#include <utils_def.h>

/*
 * RMM implements v1.0 and v1.1 RSI ABIs and supports both. This list must be
 * kept in ascending order.
 */
static const unsigned long rsi_revisions_supported[] = {
	MAKE_RSI_REVISION(1UL, 0UL),
#ifdef RMM_V1_1
	MAKE_RSI_REVISION(1UL, 1UL)
#endif
};
#define RSI_REVISIONS_COUNT	ARRAY_SIZE(rsi_revisions_supported)

COMPILER_ASSERT(RSI_REVISIONS_COUNT >= 1U);

static bool is_rsi_revision_supported(unsigned long rsi_version)
{
	/* cppcheck-suppress misra-c2012-14.2 */
	for (unsigned int i = 0U; i < RSI_REVISIONS_COUNT; i++) {
		if (rsi_version == rsi_revisions_supported[i]) {
			return true;
		}
	}

	return false;
}

unsigned long rsi_get_highest_supported_version(void)
{
	return rsi_revisions_supported[RSI_REVISIONS_COUNT - 1U];
}

/*
 * handle_rsi_version
 *
 * Input:
 * rec->reg[1]		- Requested RSI revision
 *
 * Output values:
 * res->smc_res.x[0]	- Command return status
 * res->smc_res.x[1]	- Lower supported RSI revision
 * res->smc_res.x[2]	- Higher supported RSI revision
 */
void handle_rsi_version(struct rec *rec, struct rsi_result *res)
{
	unsigned long rsi_version;
	unsigned long rsi_revision_higher;
	struct rec_plane *plane = rec_active_plane(rec);

	rsi_version = plane->regs[1];
	res->action = UPDATE_REC_RETURN_TO_REALM;

	rsi_revision_higher = rsi_get_highest_supported_version();
	if (is_rsi_revision_supported(rsi_version)) {
		res->smc_res.x[0] = RSI_SUCCESS;
		res->smc_res.x[1] = rsi_version;
	} else {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		res->smc_res.x[1] = rsi_revision_higher;
		/*
		 * TODO: When an intermediate version is not supported by RMM.
		 * This logic needs to be enhanced to get the highest interface
		 * revision which is both less than the requested revision and
		 * supported by the RMM.
		 */
	}

	res->smc_res.x[2] = rsi_revision_higher;
	assert(res->smc_res.x[1] <= res->smc_res.x[2]);
}

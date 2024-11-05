/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#include <assert.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <stdbool.h>
#include <utils_def.h>

/*
 * RMM implements v1.0 and v1.1 RMI ABIs and supports both. This list must be
 * kept in ascending order.
 */
static const unsigned long rmi_revisions_supported[] = {
	MAKE_RMI_REVISION(1UL, 0UL),
#ifdef RMM_V1_1
	MAKE_RMI_REVISION(1UL, 1UL)
#endif
};
#define RMI_REVISIONS_COUNT	ARRAY_SIZE(rmi_revisions_supported)

COMPILER_ASSERT(RMI_REVISIONS_COUNT >= 1U);

static bool is_rmi_revision_supported(unsigned long rmi_version)
{
	/* cppcheck-suppress misra-c2012-14.2 */
	for (unsigned int i = 0U; i < RMI_REVISIONS_COUNT; i++) {
		if (rmi_version == rmi_revisions_supported[i]) {
			return true;
		}
	}

	return false;
}

unsigned long rmi_get_highest_supported_version(void)
{
	return rmi_revisions_supported[RMI_REVISIONS_COUNT - 1U];
}

/*
 * smc_version
 *
 * Input:
 * rmi_version	- Requested RMI revision
 *
 * Output values:
 * x0		- Command return status
 * x1		- Lower supported RMI revision
 * x2		- Higher supported RMI revision
 */
void smc_version(unsigned long rmi_version, struct smc_result *res)
{
	unsigned long rmi_revision_higher;

	rmi_revision_higher = rmi_get_highest_supported_version();
	if (is_rmi_revision_supported(rmi_version)) {
		res->x[0] = RMI_SUCCESS;
		res->x[1] = rmi_version;
	} else {
		res->x[0] = RMI_ERROR_INPUT;
		res->x[1] = rmi_revision_higher;
		/*
		 * TODO: When an intermediate version is not supported by RMM.
		 * This logic needs to be enhanced to get the highest interface
		 * revision which is both less than the requested revision and
		 * supported by the RMM.
		 */
	}

	res->x[2] = rmi_revision_higher;
	assert(res->x[1] <= res->x[2]);
}

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <arm_memory.h>
#include <assert.h>
#include <platform_api.h>

static struct arm_memory_layout arm_dram;
static struct arm_memory_layout arm_dev_ncoh;
static struct arm_memory_layout arm_dev_coh;

/* cppcheck-suppress misra-c2012-8.7 */
struct arm_memory_layout *arm_get_dram_layout(void)
{
	return &arm_dram;
}

/* cppcheck-suppress misra-c2012-8.7 */
struct arm_memory_layout *arm_get_dev_ncoh_layout(void)
{
	return &arm_dev_ncoh;
}

/* cppcheck-suppress misra-c2012-8.7 */
struct arm_memory_layout *arm_get_dev_coh_layout(void)
{
	return &arm_dev_coh;
}

/* Return the static Arm platform memory bank array for the RMI @category. */
/* cppcheck-suppress misra-c2012-8.7 */
const struct plat_memory_bank *plat_get_mem_banks(
					unsigned long category,
					unsigned long *num_banks)
{
	const struct arm_memory_layout *layout;

	assert(is_mmu_enabled());

	if (num_banks == NULL) {
		return NULL;
	}

	switch (category) {
	case RMI_MEM_CATEGORY_CONVENTIONAL:
		layout = &arm_dram;
		break;
	case RMI_MEM_CATEGORY_DEV_NCOH:
		layout = &arm_dev_ncoh;
		break;
	case RMI_MEM_CATEGORY_DEV_COH:
		layout = &arm_dev_coh;
		break;
	default:
		return NULL;
	}

	*num_banks = layout->num_banks;
	return layout->bank;
}

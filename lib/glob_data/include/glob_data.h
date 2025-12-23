/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef GLOBDATA_H
#define GLOBDATA_H

#include <stddef.h>
#include <stdint.h>
#include <utils_def.h>
#include <xlat_low_va.h>

#define GLOBDATA_VERSION		1UL
#define GLOB_DATA_MAX_SIZE		(round_up(sizeof(struct glob_data), GRANULE_SIZE))

/* NOLINTNEXTLINE(clang-analyzer-optin.performance.Padding) as fields are in logical order*/
struct glob_data {
	unsigned long version;

	struct xlat_low_va_info low_va_info;

	uintptr_t glob_data_pa;
	uintptr_t glob_data_va;
	size_t glob_data_size;

	/* Memory for struct granule array */
	uintptr_t granules_pa;
	uintptr_t granules_va;
	size_t granules_size;

	/* Memory for struct dev_granule array */
	uintptr_t dev_granules_pa;
	uintptr_t dev_granules_va;
	size_t dev_granules_size;

	/* Memory for SMMU driver */
	uintptr_t smmu_driv_hdl_va;
	uintptr_t smmu_driv_hdl_pa;
	size_t smmu_driv_hdl_sz;
};

uintptr_t glob_data_init(struct glob_data *gl,
		unsigned long max_gr, unsigned long max_dev_gr);

uintptr_t glob_data_get_granules_va(size_t *alloc_size);
uintptr_t glob_data_get_dev_granules_va(size_t *alloc_size);
uintptr_t glob_data_get_smmu_driv_hdl_va(size_t *alloc_size);

#endif

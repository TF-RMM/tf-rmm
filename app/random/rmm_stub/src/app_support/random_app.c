/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_common.h>
#include <assert.h>
#include <cpuid.h>
#include <debug.h>
#include <entropy.h>
#include <errno.h>
#include <limits.h>
/* TODO: Somehow fix the confusing naming here: */
#include <random_app.h>
#include <random_defs.h>
#include <simd.h>

#define RANDOM_APP_PAGE_COUNT 5U

static unsigned char rmm_random_app_pages
		[MAX_CPUS][RANDOM_APP_PAGE_COUNT][GRANULE_SIZE] __aligned(GRANULE_SIZE);
static struct app_data_cfg rmm_random_app_datas[MAX_CPUS] __aligned(GRANULE_SIZE);
static bool random_app_init_done[MAX_CPUS];

static void get_random_seed(uintptr_t output, size_t len)
{
	assert(!random_app_init_done[my_cpuid()]);

	/* Enforce `len` is a multiple of 8 and `output` is 8-byte aligned. */
	assert(((len & 7UL) == 0UL) && ((output & 7UL) == 0UL));

	while (len != 0UL) {
		while (!arch_collect_entropy((uint64_t *)output)) {
		}

		len -= sizeof(uint64_t);
		output += sizeof(uint64_t);
	}
}

static int random_app_init(
	struct app_data_cfg *app_data,
	uintptr_t granule_pas[],
	size_t granule_pa_count,
	void *granule_va_start)
{
	assert(!random_app_init_done[my_cpuid()]);
	return app_init_data(app_data,
				  RMM_RANDOM_APP_ID,
				  granule_pas,
				  granule_pa_count,
				  granule_va_start);
}

static int random_app_prng_init(struct app_data_cfg *app_data,
			 uint8_t *seed,
			 size_t seed_len)
{
	unsigned long ret;

	assert(!random_app_init_done[my_cpuid()]);
	if (seed_len > GRANULE_SIZE) {
		return - EINVAL;
	}

	app_map_shared_page(app_data);
	assert(app_data->el2_shared_page != NULL);
	(void)memcpy(app_data->el2_shared_page, (void *)seed, seed_len);
	app_unmap_shared_page(app_data);
	SIMD_FPU_ALLOW(
	ret = app_run(app_data, RANDOM_APP_FUNC_ID_PRNG_INIT, seed_len, 0, 0, 0));

	assert(app_data->exit_flag != APP_EXIT_SVC_YIELD_FLAG);

	if (ret > (unsigned long)INT_MAX) {
		return - EINVAL;
	} else {
		return (int)ret;
	}
}

int random_app_prng_get_random(struct app_data_cfg *app_data, uint8_t *buf, size_t output_size)
{
	unsigned long ret;
	unsigned int cpuid = my_cpuid();

	if (!random_app_init_done[cpuid]) {
		return - EINVAL;
	}

	if (output_size > GRANULE_SIZE) {
		return - EINVAL;
	}
	SIMD_FPU_ALLOW(
	ret = app_run(app_data, RANDOM_APP_FUNC_ID_PRNG_GET_RANDOM, output_size, 0, 0, 0));

	assert(app_data->exit_flag != APP_EXIT_SVC_YIELD_FLAG);

	if (ret > (unsigned long)INT_MAX) {
		return - EINVAL;
	}
	if (ret != 0UL) {
		return (int)ret;
	}

	app_map_shared_page(app_data);
	assert(app_data->el2_shared_page != NULL);
	(void)memcpy((void *)buf, app_data->el2_shared_page, output_size);
	app_unmap_shared_page(app_data);

	return 0;
}

/* Add declaration to prevent static checker error */
void random_app_get_bss(uintptr_t *bss_pa, size_t *bss_size);

void random_app_get_bss(uintptr_t *bss_pa, size_t *bss_size)
{
	static char random_app_bss[GRANULE_SIZE] __aligned(GRANULE_SIZE);
	*bss_pa = (uintptr_t)random_app_bss;
	*bss_size = sizeof(random_app_bss);
}

void random_app_init_prng(void)
{
	int ret;
	unsigned int cpuid = my_cpuid();

	/* Need to be initialised only once as part of cold or warm boot. */
	if (random_app_init_done[cpuid]) {
		return;
	}

	/* Initialise the random applications for this CPU */
	uintptr_t granule_pas[RANDOM_APP_PAGE_COUNT];

	for (size_t i = 0; i < RANDOM_APP_PAGE_COUNT; ++i) {
		granule_pas[i] = (uintptr_t)&rmm_random_app_pages[cpuid][i][0];
	}

	ret = random_app_init(&rmm_random_app_datas[cpuid],
			granule_pas,
			RANDOM_APP_PAGE_COUNT,
			&rmm_random_app_pages[cpuid][0][0]);
	if (ret != 0) {
		return;
	}

	/*
	 * Initialise the prng for generating random numbers.
	 */
	uint8_t seed[128] = {0};

	get_random_seed((uintptr_t)seed, sizeof(seed));

	ret = random_app_prng_init(&rmm_random_app_datas[cpuid], seed, sizeof(seed));
	if (ret != 0) {
		return;
	}
	VERBOSE("rnd[%u] initialised with seed = 0x%016lx...\n", cpuid, *((unsigned long *)seed));

	random_app_init_done[cpuid] = true;
}

struct app_data_cfg *random_app_get_data_cfg(void)
{
	unsigned int cpuid = my_cpuid();

	assert(random_app_init_done[cpuid]);
	return & rmm_random_app_datas[cpuid];
}


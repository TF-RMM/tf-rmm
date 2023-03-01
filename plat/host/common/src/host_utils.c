/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <host_defs.h>
#include <host_utils.h>
#include <plat_common.h>
#include <string.h>
#include <xlat_tables.h>

static struct sysreg_data sysregs[SYSREG_MAX_CBS];
static unsigned int installed_cb_idx;
static unsigned int current_cpuid;

/*
 * Allocate memory to emulate physical memory to initialize the
 * granule library.
 */
static unsigned char granules_buffer[HOST_MEM_SIZE] __aligned(GRANULE_SIZE);

/*
 * Generic callback to access a sysreg for reading.
 */
static u_register_t sysreg_rd_cb(u_register_t *reg)
{
	return *reg;
}

/*
 * Generic callback to access a sysreg for writing.
 */
static void sysreg_wr_cb(u_register_t val, u_register_t *reg)
{
	*reg = val;
}

struct sysreg_cb *host_util_get_sysreg_cb(char *name)
{
	for (unsigned int i = 0U; i < SYSREG_MAX_CBS; i++) {
		if (strncmp(name, &sysregs[i].name[0],
			    MAX_SYSREG_NAME_LEN) == 0) {

			/*
			 * Get a pointer to the register value for the
			 * current CPU.
			 */
			sysregs[i].callbacks.reg =
					&(sysregs[i].value[current_cpuid]);
			return &sysregs[i].callbacks;
		}
	}

	return (struct sysreg_cb *)NULL;
}

int host_util_set_sysreg_cb(char *name, rd_cb_t rd_cb, wr_cb_t wr_cb,
			    u_register_t init)
{
	if (installed_cb_idx < SYSREG_MAX_CBS) {
		sysregs[installed_cb_idx].callbacks.rd_cb = rd_cb;
		sysregs[installed_cb_idx].callbacks.wr_cb = wr_cb;
		sysregs[installed_cb_idx].callbacks.reg =
							(u_register_t *)NULL;

		for (unsigned int i = 0U; i < MAX_CPUS; i++) {
			sysregs[installed_cb_idx].value[i] = init;
		}

		(void)strncpy(&(sysregs[installed_cb_idx].name[0]),
			      &name[0], MAX_SYSREG_NAME_LEN);

		/*
		 * Add a string termination character in case the
		 * name were truncated.
		 */
		sysregs[installed_cb_idx].name[MAX_SYSREG_NAME_LEN] = '\0';

		++installed_cb_idx;

		return 0;
	}

	return -ENOMEM;
}

void host_util_reset_all_sysreg_cb(void)
{

	(void)memset((void *)sysregs, 0,
		     sizeof(struct sysreg_data) * SYSREG_MAX_CBS);

	installed_cb_idx = 0U;
}

int host_util_set_default_sysreg_cb(char *name, u_register_t init)
{
	return host_util_set_sysreg_cb(name, &sysreg_rd_cb,
				       &sysreg_wr_cb, init);
}

unsigned long host_util_get_granule_base(void)
{
	return (unsigned long)granules_buffer;
}

void host_util_set_cpuid(unsigned int cpuid)
{
	assert(cpuid < MAX_CPUS);

	current_cpuid = cpuid;
}

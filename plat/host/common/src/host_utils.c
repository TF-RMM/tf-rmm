/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <debug.h>
#include <errno.h>
#include <host_defs.h>
#include <host_utils.h>
#include <plat_common.h>
#include <string.h>
#include <xlat_tables.h>

static struct sysreg_cb callbacks[SYSREG_MAX_CBS];
static unsigned int installed_cb_idx;

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
		if (strncmp(name, &callbacks[i].sysreg[0],
			    MAX_SYSREG_NAME_LEN) == 0) {
			return &callbacks[i];
		}
	}

	return (struct sysreg_cb *)NULL;
}

int host_util_set_sysreg_cb(char *name, rd_cb_t rd_cb, wr_cb_t wr_cb,
			    u_register_t init)
{
	if (installed_cb_idx < SYSREG_MAX_CBS) {
		callbacks[installed_cb_idx].rd_cb = rd_cb;
		callbacks[installed_cb_idx].wr_cb = wr_cb;
		callbacks[installed_cb_idx].value = init;

		(void)strncpy(&(callbacks[installed_cb_idx].sysreg[0]),
			      &name[0], MAX_SYSREG_NAME_LEN);

		/*
		 * Add a string termination character in case the
		 * name were truncated.
		 */
		callbacks[installed_cb_idx].sysreg[MAX_SYSREG_NAME_LEN] = '\0';

		++installed_cb_idx;

		return 0;
	}

	return -ENOMEM;
}

void host_util_reset_all_sysreg_cb(void)
{

	(void)memset((void *)callbacks, 0,
		     sizeof(struct sysreg_cb) * SYSREG_MAX_CBS);

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

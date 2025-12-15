/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <host_utils.h>
#include <string.h>

static struct sysreg_data sysregs[SYSREG_MAX_CBS];
static struct sysreg_data sysregs_snapshot[SYSREG_MAX_CBS];
struct cached_idreg_info cached_idreg_snapshot = {0};
static unsigned int installed_cb_idx;
static unsigned int installed_cb_idx_snapshot;
static unsigned int current_cpuid;

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

u_register_t host_read_sysreg(char *reg_name)
{
	struct sysreg_cb *callbacks = host_util_get_sysreg_cb(reg_name);

	/*
	 * Return 0UL as default value for registers which do not have
	 * a read callback installed.
	 */
	if (callbacks == NULL) {
		return 0UL;
	}

	if (callbacks->rd_cb == NULL) {
		return 0UL;
	}

	return callbacks->rd_cb(callbacks->reg);
}

void host_write_sysreg(char *reg_name, u_register_t v)
{
	struct sysreg_cb *callbacks = host_util_get_sysreg_cb(reg_name);

	/*
	 * Ignore the write if the register does not have a write
	 * callback installed.
	 */
	if (callbacks != NULL) {
		if (callbacks->wr_cb != NULL) {
			callbacks->wr_cb(v, callbacks->reg);
		}
	}
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
	size_t name_len;
	unsigned int cb_idx = 0U;

	name_len = strlen(&name[0]);
	if (name_len >= MAX_SYSREG_NAME_LEN) {
		name_len = MAX_SYSREG_NAME_LEN - 1U;
	}

	/* Find the callback index that matches the register name */
	while ((cb_idx < installed_cb_idx) &&
			(strncmp(name, &sysregs[cb_idx].name[0],
			MAX_SYSREG_NAME_LEN) != 0)) {
		cb_idx++;
	}

	if (cb_idx < SYSREG_MAX_CBS) {
		sysregs[cb_idx].callbacks.rd_cb = rd_cb;
		sysregs[cb_idx].callbacks.wr_cb = wr_cb;
		sysregs[cb_idx].callbacks.reg =	(u_register_t *)NULL;

		for (unsigned int i = 0U; i < MAX_CPUS; i++) {
			sysregs[cb_idx].value[i] = init;
		}

		if (cb_idx == installed_cb_idx) {
			/*
			 * Callback is being set for the first time, so
			 * set the register name field for the entry and
			 * increase the number of callbacks.
			 */

			(void)memcpy(&(sysregs[cb_idx].name[0]), &name[0], name_len);

			/*
			 * Add a string termination character.
			 */
			sysregs[cb_idx].name[name_len] = '\0';

			++installed_cb_idx;
		}

		return 0;
	}

	return -ENOMEM;
}

int host_util_set_default_sysreg_cb(char *name, u_register_t init)
{
	return host_util_set_sysreg_cb(name, &sysreg_rd_cb,
				       &sysreg_wr_cb, init);
}

void host_util_take_sysreg_snapshot(void)
{
	memcpy((void *)&sysregs_snapshot[0], (void *)&sysregs[0],
		sizeof(struct sysreg_data) * SYSREG_MAX_CBS);
	installed_cb_idx_snapshot = installed_cb_idx;

	memcpy((void *)&cached_idreg_snapshot,
	       (void *)&cached_idreg,
	       sizeof(cached_idreg_snapshot));
}

void host_util_restore_sysreg_snapshot(void)
{
	memcpy((void *)&sysregs[0], (void *)&sysregs_snapshot[0],
		sizeof(struct sysreg_data) * SYSREG_MAX_CBS);
	installed_cb_idx = installed_cb_idx_snapshot;

	memcpy((void *)&cached_idreg,
	       (void *)&cached_idreg_snapshot,
	       sizeof(cached_idreg));
}

void host_util_zero_sysregs_and_cbs(void)
{
	(void)memset((void *)sysregs, 0,
		     sizeof(struct sysreg_data) * SYSREG_MAX_CBS);
	ZERO_CACHED_REGS();

	installed_cb_idx = 0U;
}

void host_util_set_cpuid(unsigned int cpuid)
{
	assert(cpuid < MAX_CPUS);

	current_cpuid = cpuid;
}


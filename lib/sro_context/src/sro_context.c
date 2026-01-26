/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <cpuid.h>
#include <smc-rmi.h>
#include <spinlock.h>
#include <sro_context.h>
#include <string.h>

/*
 * Per_cpu reference to command context that is currently used by the CPU.
 */
struct cpu_sro_ctx {
	/* NULL if no SRO context is assigned to the CPU */
	struct sro_context *ctx;

	/* The unique identifier of a CPU' SRO context */
	unsigned int op_handle;
};

/* @FIXME: This memory will need to be provided by EL3 */
static struct cpu_sro_ctx cpu_sro_ctx[MAX_CPUS];

/*
 * The number of SRO contexts.
 * As a SRO context may remain allocated when RMI handle exits to host,
 * this should be considerably larger than cpu count.*/
#define SRO_CTX_COUNT	(8 * MAX_CPUS)

/* @FIXME: This memory will need to be provided by EL3 */
static struct sro_context sro_ctx[SRO_CTX_COUNT];

/* State of an SRO context */
enum sro_state {
	/* SRO is available */
	SRO_STATE_FREE,

	/* SRO is in used by a running RMI handle */
	SRO_STATE_RESERVED,

	/* SRO is reserved after exit to Host */
	SRO_STATE_SEALED
};

/* @TODO: This might be embedded inside sro_context */
static enum sro_state sro_state[SRO_CTX_COUNT];

static spinlock_t sro_spinlock;

static inline void sro_ctx_zero(unsigned int cpuid)
{
	struct sro_context *ctx = cpu_sro_ctx[cpuid].ctx;

	assert(cpuid < MAX_CPUS);
	assert(ctx != NULL);

	memset((void *)ctx, 0, sizeof(struct sro_context));
}

/*
 * Assigns a command context to the current CPU
 * It returns:
 * - RMI_BLOCKED: All SRO contexts are sealed.
 * - RMI_BUSY:    Some SRO contexts are reserved, the rest is sealed.
 * - RMI_SUCCESS: SRO context is assigned to the current CPU.
 */
unsigned long sro_ctx_reserve(unsigned long command, unsigned long xfer,
			      bool can_cancel, bool is_contig)
{
	unsigned int sealed = 0U;
	unsigned int cpuid = my_cpuid();
	unsigned long ret = RMI_BUSY;

	assert (cpu_sro_ctx[cpuid].ctx == NULL);

	spinlock_acquire(&sro_spinlock);

	for (unsigned int i = 0U; i < SRO_CTX_COUNT; i++) {
		if (sro_state[i] == SRO_STATE_FREE) {
			sro_state[i] = SRO_STATE_RESERVED;
			cpu_sro_ctx[cpuid].ctx = &sro_ctx[i];
			cpu_sro_ctx[cpuid].op_handle = i;
			sro_ctx_zero(cpuid);
			sro_ctx[i].init_command = command;
			sro_ctx[i].can_cancel = can_cancel;
			sro_ctx[i].is_contig = is_contig;
			sro_ctx[i].transfer_req = xfer;
			sro_ctx[i].reclaim_res = SRO_INVALID_RESULT;
			sro_ctx[i].pend_entries = 0UL;
			ret = RMI_SUCCESS;
			break;
		} else if (sro_state[i] == SRO_STATE_SEALED) {
			sealed++;
		}
	}

	if (sealed == SRO_CTX_COUNT) {
		ret = RMI_BLOCKED;
	}

	spinlock_release(&sro_spinlock);

	return ret;
}

/*
 * Seals the CPU's Context and returns its identifier.
 */
unsigned int sro_ctx_seal(void)
{
	unsigned int index, cpuid = my_cpuid();

	assert (cpu_sro_ctx[cpuid].ctx != NULL);
	index = cpu_sro_ctx[cpuid].op_handle;

	spinlock_acquire(&sro_spinlock);
	assert(sro_state[index] != SRO_STATE_FREE);

	sro_state[index] = SRO_STATE_SEALED;
	spinlock_release(&sro_spinlock);

	cpu_sro_ctx[cpuid].ctx = NULL;

	return cpu_sro_ctx[cpuid].op_handle;
}

/*
 * Finds the SRO context that matches the input identifier, transition it
 * from SRO_STATE_SEALED to SRO_STATE_RESERVED and assign it to the
 * current CPU.
 */
bool sro_ctx_find(unsigned int op_handle)
{
	bool ret;
	unsigned int cpuid = my_cpuid();

	assert(cpu_sro_ctx[cpuid].ctx == NULL);

	spinlock_acquire(&sro_spinlock);

	if (op_handle >= SRO_CTX_COUNT) {
		ret = false;
		goto out;

	}

	if (sro_state[op_handle] != SRO_STATE_SEALED) {
		ret = false;
		goto out;
	}

	sro_state[op_handle] = SRO_STATE_RESERVED;
	cpu_sro_ctx[cpuid].ctx = &sro_ctx[op_handle];
	cpu_sro_ctx[cpuid].op_handle = op_handle;
	ret = true;
out:
	spinlock_release(&sro_spinlock);
	return ret;
}

/*
 * Returns pointer to the CPU's command context.
 */
struct sro_context *my_sro_ctx(void)
{
	unsigned int cpuid = my_cpuid();

	assert(cpu_sro_ctx[cpuid].ctx != NULL);
	return cpu_sro_ctx[cpuid].ctx;
}

/*
 * Releases the CPU's command context.
 */
void sro_ctx_release(void)
{
	unsigned int index, cpuid = my_cpuid();

	assert(cpu_sro_ctx[cpuid].ctx);
	index = cpu_sro_ctx[cpuid].op_handle;

	spinlock_acquire(&sro_spinlock);

	assert(sro_state[index] == SRO_STATE_RESERVED);

	sro_state[index] = SRO_STATE_FREE;
	cpu_sro_ctx[cpuid].ctx = NULL;

	spinlock_release(&sro_spinlock);
}

/*
 * Configure the next expected FID on the SRO flow.
 */
void sro_ctx_next_cmd(unsigned long fid)
{
	struct sro_context *sro = my_sro_ctx();

	assert((fid == SMC_RMI_OP_CONTINUE) || ((fid >= SMC_RMI_OP_MEM_DONATE) &&
						(fid <= SMC_RMI_OP_CANCEL)));
	sro->expected_fid = fid;
}

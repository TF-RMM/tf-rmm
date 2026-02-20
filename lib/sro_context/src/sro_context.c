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

static struct sro_ctx_pool *pool;
static struct cpu_sro_ctx cpu_sro_ctx[MAX_CPUS];
static spinlock_t sro_spinlock;

static inline void sro_ctx_zero(unsigned int cpuid)
{
	struct sro_context *ctx = (cpu_sro_ctx + cpuid)->ctx;

	assert(cpuid < MAX_CPUS);
	assert(ctx != NULL);

	memset((void *)ctx, 0, sizeof(struct sro_context));
}

void sro_ctx_init(uintptr_t va, size_t sz)
{
	assert(pool == NULL);
	assert(va != 0UL);
	assert(sz != 0);

	(void)sz;

	pool = (struct sro_ctx_pool *)va;

	/* Check is already initialized. This happens for LFA init */
	if (pool->init) {
		return;
	}

	pool->ctx_count = MAX_CPUS * SRO_CTX_PER_CPU;

	/* The sro_context array follows the pool header in memory */
	pool->ctxs = (struct sro_context *)(va + sizeof(*pool));

	assert((uintptr_t)(pool->ctxs + pool->ctx_count) <= (va + sz));

	/* Initialize all context states to free */
	for (unsigned long i = 0UL; i < pool->ctx_count; i++) {
		pool->ctxs[i].state = SRO_STATE_FREE;
	}

	pool->init = true;
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

	assert((pool != NULL) && pool->init);
	assert (cpu_sro_ctx[cpuid].ctx == NULL);

	spinlock_acquire(&sro_spinlock);

	for (unsigned long i = 0UL; i < pool->ctx_count; i++) {
		if (pool->ctxs[i].state == SRO_STATE_FREE) {
			(cpu_sro_ctx + cpuid)->ctx = pool->ctxs + i;
			(cpu_sro_ctx + cpuid)->op_handler = (unsigned int)i;
			sro_ctx_zero(cpuid);
			pool->ctxs[i].state = SRO_STATE_RESERVED;
			pool->ctxs[i].init_command = command;
			pool->ctxs[i].can_cancel = can_cancel;
			pool->ctxs[i].is_contig = is_contig;
			pool->ctxs[i].transfer_req = xfer;
			pool->ctxs[i].reclaim_res = SRO_INVALID_RESULT;
			pool->ctxs[i].pend_entries = 0UL;
			ret = RMI_SUCCESS;
			break;
		} else if (pool->ctxs[i].state == SRO_STATE_SEALED) {
			sealed++;
		}
	}

	if ((unsigned long)sealed == pool->ctx_count) {
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
	struct cpu_sro_ctx *current_cpu_ctx = (cpu_sro_ctx + cpuid);

	assert((pool != NULL) && pool->init);
	assert(current_cpu_ctx->ctx != NULL);
	index = current_cpu_ctx->op_handler;

	spinlock_acquire(&sro_spinlock);
	assert(pool->ctxs[index].state != SRO_STATE_FREE);

	pool->ctxs[index].state = SRO_STATE_SEALED;
	spinlock_release(&sro_spinlock);

	current_cpu_ctx->ctx = NULL;

	return current_cpu_ctx->op_handler;
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
	struct cpu_sro_ctx *current_cpu_ctx = (cpu_sro_ctx + cpuid);

	assert((pool != NULL) && pool->init);

	spinlock_acquire(&sro_spinlock);

	if (op_handle >= pool->ctx_count) {
		ret = false;
		goto out;

	}

	if (pool->ctxs[op_handle].state != SRO_STATE_SEALED) {
		ret = false;
		goto out;
	}

	pool->ctxs[op_handle].state = SRO_STATE_RESERVED;
	current_cpu_ctx->ctx = (pool->ctxs + op_handle);
	current_cpu_ctx->op_handler = op_handle;
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

	assert((pool != NULL) && pool->init);
	assert((cpu_sro_ctx + cpuid)->ctx != NULL);
	return (cpu_sro_ctx + cpuid)->ctx;
}

/*
 * Releases the CPU's command context.
 */
void sro_ctx_release(void)
{
	unsigned int index, cpuid = my_cpuid();
	struct cpu_sro_ctx *current_cpu_ctx = (cpu_sro_ctx + cpuid);

	assert((pool != NULL) && pool->init);
	assert(current_cpu_ctx->ctx != NULL);

	index = current_cpu_ctx->op_handler;

	spinlock_acquire(&sro_spinlock);

	assert(pool->ctxs[index].state == SRO_STATE_RESERVED);

	pool->ctxs[index].state = SRO_STATE_FREE;
	current_cpu_ctx->ctx = NULL;

	spinlock_release(&sro_spinlock);
}

/*
 * Configure the next expected FID on the SRO flow.
 */
void sro_ctx_next_cmd(unsigned long fid)
{
	struct sro_context *sro = my_sro_ctx();

	assert((pool != NULL) && pool->init);
	assert((fid == SMC_RMI_OP_CONTINUE) || ((fid >= SMC_RMI_OP_MEM_DONATE) &&
						(fid <= SMC_RMI_OP_CANCEL)));
	sro->expected_fid = fid;
}

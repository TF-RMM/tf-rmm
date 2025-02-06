/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PMU_H
#define PMU_H

#include <arch_helpers.h>
#include <utils_def.h>

struct rmi_rec_exit;
struct rec;

struct pmev_regs {
	unsigned long pmevcntr_el0;
	unsigned long pmevtyper_el0;
};

/*
 * PMU context structure.
 * Align on cache writeback granule to minimise cache line
 * thashing when allocated as an array for use by each CPU.
 */
struct pmu_state {
	unsigned long pmcr_el0;
	unsigned long pmccfiltr_el0;
	unsigned long pmccntr_el0;
	unsigned long pmcntenset_el0;
	unsigned long pmintenset_el1;
	unsigned long pmovsset_el0;
	unsigned long pmselr_el0;
	unsigned long pmuserenr_el0;

	struct pmev_regs pmev_regs[31];

} __aligned(CACHE_WRITEBACK_GRANULE);

void pmu_save_state(struct pmu_state *pmu, unsigned int num_cnts);
void pmu_restore_state(struct pmu_state *pmu, unsigned int num_cnts);
bool pmu_is_ovf_set(void);

#endif /* PMU_H */

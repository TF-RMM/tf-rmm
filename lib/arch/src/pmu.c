/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <arch_helpers.h>
#include <assert.h>
#include <pmu.h>
#include <smc-rmi.h>

/* Clear bits P0-P30, C and F0 */
#define PMU_CLEAR_ALL	0x1FFFFFFFFUL

#define READ_PMEV_EL0(n) {					     \
	case (n):							     \
	pmu->pmev_regs[n].pmevcntr_el0 = read_pmevcntr##n##_el0();   \
	pmu->pmev_regs[n].pmevtyper_el0 = read_pmevtyper##n##_el0(); \
}

#define WRITE_PMEV_EL0(n) {					   \
	case (n):							   \
	write_pmevcntr##n##_el0(pmu->pmev_regs[n].pmevcntr_el0);   \
	write_pmevtyper##n##_el0(pmu->pmev_regs[n].pmevtyper_el0); \
}

/*
 * Save PMU context to memory with number of event counters
 * passed in 'num_cnts' and disable all event counters.
 */
void pmu_save_state(struct pmu_state *pmu, unsigned int num_cnts)
{
	assert(pmu != NULL);

	pmu->pmccfiltr_el0 = read_pmccfiltr_el0();
	pmu->pmccntr_el0 = read_pmccntr_el0();
	pmu->pmcntenset_el0 = read_pmcntenset_el0();
	pmu->pmcntenclr_el0 = read_pmcntenclr_el0();
	pmu->pmintenset_el1 = read_pmintenset_el1();
	pmu->pmintenclr_el1 = read_pmintenclr_el1();
	pmu->pmovsset_el0 = read_pmovsset_el0();
	pmu->pmovsclr_el0 = read_pmovsclr_el0();
	pmu->pmselr_el0 = read_pmselr_el0();
	pmu->pmuserenr_el0 = read_pmuserenr_el0();
	pmu->pmxevcntr_el0 = read_pmxevcntr_el0();
	pmu->pmxevtyper_el0 = read_pmxevtyper_el0();

	if (num_cnts != 0UL) {
		num_cnts--;
		switch (num_cnts) {
		READ_PMEV_EL0(30);
		READ_PMEV_EL0(29);
		READ_PMEV_EL0(28);
		READ_PMEV_EL0(27);
		READ_PMEV_EL0(26);
		READ_PMEV_EL0(25);
		READ_PMEV_EL0(24);
		READ_PMEV_EL0(23);
		READ_PMEV_EL0(22);
		READ_PMEV_EL0(21);
		READ_PMEV_EL0(20);
		READ_PMEV_EL0(19);
		READ_PMEV_EL0(18);
		READ_PMEV_EL0(17);
		READ_PMEV_EL0(16);
		READ_PMEV_EL0(15);
		READ_PMEV_EL0(14);
		READ_PMEV_EL0(13);
		READ_PMEV_EL0(12);
		READ_PMEV_EL0(11);
		READ_PMEV_EL0(10);
		READ_PMEV_EL0(9);
		READ_PMEV_EL0(8);
		READ_PMEV_EL0(7);
		READ_PMEV_EL0(6);
		READ_PMEV_EL0(5);
		READ_PMEV_EL0(4);
		READ_PMEV_EL0(3);
		READ_PMEV_EL0(2);
		READ_PMEV_EL0(1);
		default:
		READ_PMEV_EL0(0);
		}
	}
}

/*
 * Restore PMU context from memory with
 * number of event counters passed in 'num_cnts'.
 */
void pmu_restore_state(struct pmu_state *pmu, unsigned int num_cnts)
{
	assert(pmu != NULL);

	write_pmccfiltr_el0(pmu->pmccfiltr_el0);
	write_pmccntr_el0(pmu->pmccntr_el0);
	write_pmcntenset_el0(pmu->pmcntenset_el0);
	write_pmcntenclr_el0(pmu->pmcntenclr_el0 ^ PMU_CLEAR_ALL);
	write_pmintenset_el1(pmu->pmintenset_el1);
	write_pmintenclr_el1(pmu->pmintenclr_el1 ^ PMU_CLEAR_ALL);
	write_pmovsset_el0(pmu->pmovsset_el0);
	write_pmovsclr_el0(pmu->pmovsclr_el0 ^ PMU_CLEAR_ALL);
	write_pmselr_el0(pmu->pmselr_el0);
	write_pmuserenr_el0(pmu->pmuserenr_el0);
	write_pmxevcntr_el0(pmu->pmxevcntr_el0);
	write_pmxevtyper_el0(pmu->pmxevtyper_el0);

	if (num_cnts != 0U) {
		num_cnts--;
		switch (num_cnts) {
		WRITE_PMEV_EL0(30);
		WRITE_PMEV_EL0(29);
		WRITE_PMEV_EL0(28);
		WRITE_PMEV_EL0(27);
		WRITE_PMEV_EL0(26);
		WRITE_PMEV_EL0(25);
		WRITE_PMEV_EL0(24);
		WRITE_PMEV_EL0(23);
		WRITE_PMEV_EL0(22);
		WRITE_PMEV_EL0(21);
		WRITE_PMEV_EL0(20);
		WRITE_PMEV_EL0(19);
		WRITE_PMEV_EL0(18);
		WRITE_PMEV_EL0(17);
		WRITE_PMEV_EL0(16);
		WRITE_PMEV_EL0(15);
		WRITE_PMEV_EL0(14);
		WRITE_PMEV_EL0(13);
		WRITE_PMEV_EL0(12);
		WRITE_PMEV_EL0(11);
		WRITE_PMEV_EL0(10);
		WRITE_PMEV_EL0(9);
		WRITE_PMEV_EL0(8);
		WRITE_PMEV_EL0(7);
		WRITE_PMEV_EL0(6);
		WRITE_PMEV_EL0(5);
		WRITE_PMEV_EL0(4);
		WRITE_PMEV_EL0(3);
		WRITE_PMEV_EL0(2);
		WRITE_PMEV_EL0(1);
		default:
		WRITE_PMEV_EL0(0);
		}
	}
}

/*
 * Expose Realm PMU state on REC exit.
 */
void pmu_update_rec_exit(struct rmi_rec_exit *rec_exit)
{
	assert(rec_exit != NULL);

	if (((read_pmovsset_el0() & read_pmintenset_el1() &
	     read_pmcntenset_el0()) != 0UL) &&
	     ((read_pmcr_el0() & PMCR_EL0_E_BIT) != 0UL)) {
		rec_exit->pmu_ovf_status = RMI_PMU_OVERFLOW_ACTIVE;
	} else {
		rec_exit->pmu_ovf_status = RMI_PMU_OVERFLOW_NOT_ACTIVE;
	}
}

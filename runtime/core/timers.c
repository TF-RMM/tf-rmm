/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <rec.h>
#include <smc-rmi.h>
#include <stdbool.h>
#include <timers.h>

/*
 * Check that timer output is asserted:
 * Timer enabled: CNTx_CTL_ENABLE = 1
 * Timer condition is met: CNTx_CTL_ISTATUS = 1
 * Timer interrupt is not masked: CNTx_CTL_IMASK = 0
 */
#define TIMER_ASSERTED(reg)						\
	(((reg) &							\
	(CNTx_CTL_ENABLE | CNTx_CTL_ISTATUS | CNTx_CTL_IMASK)) ==	\
	(CNTx_CTL_ENABLE | CNTx_CTL_ISTATUS))

/* Which plane timer to report on REC return */
struct report_timer {
	bool value;
};

/* Possible status of EL1 Timer on Plane 0 */
#define P0_ACTIVE		(true)
#define P0_INACTIVE		(false)

/* Possible status of EL1 Timer on Plane N */
#define PN_ACTIVE		(true)
#define PN_INACTIVE		(false)

/* Which Timer will expire earliest */
#define EARLIEST_PN		(true)
#define EARLIEST_P0		(false)

/* Which plane timer to report on REC return */
#define REPORT_P0		(true)
#define REPORT_PN		(false)

#define GENERATE_ENCODE_INDEX(_p0_active, _pn_active, _earliest_cval)	\
	(((_p0_active) ? (1U << 2U) : 0U) |				\
	 ((_pn_active) ? (1U << 1U) : 0U) |				\
	 ((_earliest_cval) ? (1U << 0U) : 0U))

#define TIMER_REPORT_ENCODE(_p0_active, _pn_active, _earliest_cval, _p_reported)	\
	[GENERATE_ENCODE_INDEX(_p0_active, _pn_active, _earliest_cval)] =		\
		{ .value = (_p_reported)}

/*
 * Check the pending state of the timers.
 *
 * When a timer output is asserted, its interrupt signal should be masked at
 * EL2 when running the Realm to prevent the physical interrupt from
 * continuously exiting the Realm.
 *
 * When a timer output is not asserted, the interrupt signal should be
 * unmasked such that if the timer output becomes asserted again, an exit from
 * the Realm happens due to a physical IRQ and we can inject a virtual
 * interrupt again.
 */
bool check_pending_timers(struct rec_plane *plane)
{
	unsigned long cntv_ctl = read_cntv_ctl_el02();
	unsigned long cntp_ctl = read_cntp_ctl_el02();
	unsigned long cnthctl_old;

	assert(plane != NULL);
	assert(plane->sysregs != NULL);

	cnthctl_old = plane->sysregs->cnthctl_el2;

	if (TIMER_ASSERTED(cntv_ctl)) {
		plane->sysregs->cnthctl_el2 |= CNTHCTL_EL2_CNTVMASK;
	} else {
		plane->sysregs->cnthctl_el2 &= ~CNTHCTL_EL2_CNTVMASK;
	}

	if (TIMER_ASSERTED(cntp_ctl)) {
		plane->sysregs->cnthctl_el2 |= CNTHCTL_EL2_CNTPMASK;
	} else {
		plane->sysregs->cnthctl_el2 &= ~CNTHCTL_EL2_CNTPMASK;
	}

	if (cnthctl_old != plane->sysregs->cnthctl_el2) {
		write_cnthctl_el2(plane->sysregs->cnthctl_el2);
		isb();
	}

	/*
	 * We don't want to run the Realm just to immediately exit due a
	 * physical interrupt caused by one of the timer interrupts not having
	 * been retired from the CPU interface yet. Check that the interrupts
	 * are retired before entering the Realm.
	 */
	while (true) {
		unsigned long hppir = read_icc_hppir1_el1();
		unsigned int intid =
			(unsigned int)EXTRACT(ICC_HPPIR1_EL1_INTID, hppir);

		if (!((((plane->sysregs->cnthctl_el2 & CNTHCTL_EL2_CNTVMASK) != 0UL) &&
			(intid == EL1_VIRT_TIMER_PPI)) ||
		      (((plane->sysregs->cnthctl_el2 & CNTHCTL_EL2_CNTPMASK) != 0UL) &&
			(intid == EL1_PHYS_TIMER_PPI)))) {
			break;
		}
	}

	/*
	 * Check if the timers changed their output status based on
	 * the previously saved timer state at the last Realm exit.
	 */
	return (TIMER_ASSERTED(cntv_ctl) !=
		TIMER_ASSERTED(plane->sysregs->pp_sysregs.cntv_ctl_el0)) ||
		(TIMER_ASSERTED(cntp_ctl) !=
		 TIMER_ASSERTED(plane->sysregs->pp_sysregs.cntp_ctl_el0));
}

/* Table to determine which EL1 timer to report on REC exit */
static const struct report_timer plane_report[] = {
	/*		     P0 Timer     PN Timer    Earliest CVAL  Report to Host */
	TIMER_REPORT_ENCODE(P0_INACTIVE, PN_INACTIVE,  EARLIEST_P0,    REPORT_P0),
	TIMER_REPORT_ENCODE(P0_INACTIVE, PN_INACTIVE,  EARLIEST_PN,    REPORT_P0),
	TIMER_REPORT_ENCODE(P0_INACTIVE, PN_ACTIVE,    EARLIEST_P0,    REPORT_PN),
	TIMER_REPORT_ENCODE(P0_INACTIVE, PN_ACTIVE,    EARLIEST_PN,    REPORT_PN),
	TIMER_REPORT_ENCODE(P0_ACTIVE,   PN_INACTIVE,  EARLIEST_P0,    REPORT_P0),
	TIMER_REPORT_ENCODE(P0_ACTIVE,   PN_INACTIVE,  EARLIEST_PN,    REPORT_P0),
	TIMER_REPORT_ENCODE(P0_ACTIVE,   PN_ACTIVE,    EARLIEST_P0,    REPORT_P0),
	TIMER_REPORT_ENCODE(P0_ACTIVE,   PN_ACTIVE,    EARLIEST_PN,    REPORT_PN)
};

void report_timer_state_to_ns(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	unsigned long cntv_ctl = read_cntv_ctl_el02();
	unsigned long cntv_cval = read_cntv_cval_el02() - read_cntvoff_el2();
	unsigned long cntp_ctl = read_cntp_ctl_el02();
	unsigned long cntp_cval = read_cntp_cval_el02() - read_cntpoff_el2();

	if (!rec_is_plane_0_active(rec)) {
		/*
		 * If Plane 0 was active, we would have reported P0 EL1 timer.
		 * On this case, thought, we need to determine which EL1 timer
		 * to report.
		 */
		STRUCT_TYPE sysreg_state *sysregs = rec->plane[PLANE_0_ID].sysregs;
		unsigned long p0_cntv_cval = sysregs->pp_sysregs.cntv_cval_el0 -
					     sysregs->cntvoff_el2;
		unsigned long p0_cntv_ctl = sysregs->pp_sysregs.cntv_ctl_el0;
		unsigned long p0_cntp_cval = sysregs->pp_sysregs.cntp_cval_el0 -
					     sysregs->cntpoff_el2;
		unsigned long p0_cntp_ctl = sysregs->pp_sysregs.cntp_ctl_el0;

		/* Whether PN has the earliest timer to expire */
		bool pn_earliest_virt_cval = (cntv_cval < p0_cntv_cval);
		bool pn_earliest_phys_cval = (cntp_cval < p0_cntp_cval);

		/* Which plane timer to report */
		bool virt_report = plane_report[
			GENERATE_ENCODE_INDEX(is_timer_enabled(p0_cntv_ctl),
					is_timer_enabled(cntv_ctl),
					pn_earliest_virt_cval)].value;
		bool phys_report = plane_report[
			GENERATE_ENCODE_INDEX(is_timer_enabled(p0_cntp_ctl),
					is_timer_enabled(cntp_ctl),
					pn_earliest_phys_cval)].value;

		if (virt_report == REPORT_P0) {
			cntv_cval = p0_cntv_cval;
			cntv_ctl = p0_cntv_ctl;
		}

		if (phys_report == REPORT_P0) {
			cntp_cval = p0_cntp_cval;
			cntp_ctl = p0_cntp_cval;
		}
	}

	/* Expose Realm EL1 timer state */
	rec_exit->cntv_ctl = cntv_ctl;
	rec_exit->cntv_cval = cntv_cval;
	rec_exit->cntp_ctl = cntp_ctl;
	rec_exit->cntp_cval = cntp_cval;
}

void hyp_timer_save_state(struct timer_state *el2_timer)
{
	el2_timer->phys_ctl = read_cnthp_ctl_el2();
	el2_timer->phys_cval = read_cnthp_cval_el2();
	el2_timer->virt_ctl = read_cnthv_ctl_el2();
	el2_timer->virt_cval = read_cnthv_cval_el2();
}

void hyp_timer_restore_state(struct timer_state *el2_timer)
{
	write_cnthp_ctl_el2(el2_timer->phys_ctl);
	write_cnthp_cval_el2(el2_timer->phys_cval);
	write_cnthv_ctl_el2(el2_timer->virt_ctl);
	write_cnthv_cval_el2(el2_timer->virt_cval);
}

bool is_timer_enabled(unsigned long cnt_ctl)
{
	return ((cnt_ctl) & (CNTx_CTL_ENABLE | CNTx_CTL_IMASK)) == CNTx_CTL_ENABLE;
}

/*
 * Select EL2 timers config between Plane 0 EL1 timers and NS EL2 timers.
 *
 * When entering a Plane N, if plane 0 has pending EL1 timers we should
 * ensure we're notified of their expiry. EL2 timers are used for this purpose,
 * but since we are also meant to keep track of NS EL2 timers, we must keep the
 * first one to expire in each timer configuration.
 */
void multiplex_el2_timer(struct rec *rec)
{
	/* Plane 0 time information */
	STRUCT_TYPE sysreg_state *sysregs = rec->plane[PLANE_0_ID].sysregs;
	struct timer_state *ns_el2_timer_state = &rec->ns->el2_timer;
	unsigned long pp_cnt_cval, ns_cnt_cval, ns_cnt_ctl;

	/*
	 * Physical Timer
	 * If the EL1 timer for Plane 0 is not enabled, skip.
	 */
	if (is_timer_enabled(sysregs->pp_sysregs.cntp_ctl_el0)) {
		/* Get "real" counter value */
		pp_cnt_cval = sysregs->pp_sysregs.cntp_cval_el0 - read_cntpoff_el2();
		ns_cnt_cval = ns_el2_timer_state->phys_cval;
		ns_cnt_ctl = ns_el2_timer_state->phys_ctl;

		/* Compare with EL2 timer and set the earliest enabled one */
		if ((pp_cnt_cval < ns_cnt_cval) || !is_timer_enabled(ns_cnt_ctl)) {
			write_cnthp_cval_el2(pp_cnt_cval);
		}
	}

	/*
	 * Virtual Timer
	 * If the EL1 timer for plane 0 is not enabled, skip.
	 */
	if (is_timer_enabled(sysregs->pp_sysregs.cntv_ctl_el0)) {
		/* Get "real" counter value */
		pp_cnt_cval = sysregs->pp_sysregs.cntv_cval_el0 - read_cntvoff_el2();
		ns_cnt_cval = ns_el2_timer_state->virt_cval;
		ns_cnt_ctl = ns_el2_timer_state->virt_ctl;

		/* Compare with EL2 timer and set the earliest enabled one */
		if ((pp_cnt_cval < ns_cnt_cval) || !is_timer_enabled(ns_cnt_ctl)) {
			write_cnthv_cval_el2(pp_cnt_cval);
		}
	}
}

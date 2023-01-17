/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SMC_RMI_H
#define SMC_RMI_H

#include <measurement.h>
#include <smc.h>

/*
 * This file describes the Realm Management Interface (RMI) Application Binary
 * Interface (ABI) for SMC calls made from Non-secure state to the RMM and
 * serviced by the RMM.
 *
 * See doc/rmm_interface.md for more details.
 */

/*
 * The major version number of the RMI implementation.  Increase this whenever
 * the binary format or semantics of the SMC calls change.
 */
#define RMI_ABI_VERSION_MAJOR		(56U)

/*
 * The minor version number of the RMI implementation.  Increase this when
 * a bug is fixed, or a feature is added without breaking binary compatibility.
 */
#define RMI_ABI_VERSION_MINOR		(0U)

#define RMI_ABI_VERSION			((RMI_ABI_VERSION_MAJOR << 16U) | \
					RMI_ABI_VERSION_MINOR)

#define RMI_ABI_VERSION_GET_MAJOR(_version) ((_version) >> 16U)
#define RMI_ABI_VERSION_GET_MINOR(_version) ((_version) & 0xFFFFU)

#define SMC64_RMI_FID(_offset)		SMC64_STD_FID(RMI, _offset)

#define IS_SMC64_RMI_FID(_fid)		IS_SMC64_STD_FAST_IN_RANGE(RMI, _fid)

/*
 * The number of GPRs (starting from X0) that are
 * configured by the host when a REC is created.
 */
#define REC_CREATE_NR_GPRS		(8U)

#define REC_PARAMS_FLAG_RUNNABLE	(1UL << 0U)

/*
 * The number of GPRs (starting from X0) per voluntary exit context.
 * Per SMCCC.
 */
#define REC_EXIT_NR_GPRS		(31U)

/* RmiHashAlgorithm type */
#define RMI_HASH_ALGO_SHA256	HASH_ALGO_SHA256
#define RMI_HASH_ALGO_SHA512	HASH_ALGO_SHA512

/* Maximum number of Interrupt Controller List Registers */
#define REC_GIC_NUM_LRS			(16U)

/* Maximum number of auxiliary granules required for a REC */
#define MAX_REC_AUX_GRANULES		(16U)

#define REC_ENTRY_FLAG_EMUL_MMIO	(1UL << 0U)
#define REC_ENTRY_FLAG_INJECT_SEA	(1UL << 1U)

/* Flags to specify if WFI/WFE should be trapped to host */
#define REC_ENTRY_FLAG_TRAP_WFI		(1UL << 2U)
#define REC_ENTRY_FLAG_TRAP_WFE		(1UL << 3U)

/*
 * RmiRecExitReason represents the reason for a REC exit.
 * This is returned to NS hosts via RMI_REC_ENTER::run_ptr.
 */
#define RMI_EXIT_SYNC			(0U)
#define RMI_EXIT_IRQ			(1U)
#define RMI_EXIT_FIQ			(2U)
#define RMI_EXIT_PSCI			(3U)
#define RMI_EXIT_RIPAS_CHANGE		(4U)
#define RMI_EXIT_HOST_CALL		(5U)
#define RMI_EXIT_SERROR			(6U)

/* RmiRttEntryState represents the state of an RTTE */
#define RMI_RTT_STATE_UNASSIGNED	(0U)
#define RMI_RTT_STATE_DESTROYED		(1U)
#define RMI_RTT_STATE_ASSIGNED		(2U)
#define RMI_RTT_STATE_TABLE		(3U)
#define RMI_RTT_STATE_VALID_NS		(4U)

/* no parameters */
#define SMC_RMM_VERSION				SMC64_RMI_FID(U(0x0))

/*
 * arg0 == target granule address
 */
#define SMC_RMM_GRANULE_DELEGATE		SMC64_RMI_FID(U(0x1))

/*
 * arg0 == target granule address
 */
#define SMC_RMM_GRANULE_UNDELEGATE		SMC64_RMI_FID(U(0x2))

/* RmiDataMeasureContent type */
#define RMI_NO_MEASURE_CONTENT 0
#define RMI_MEASURE_CONTENT  1

/*
 * arg0 == data address
 * arg1 == RD address
 * arg2 == map address
 * arg3 == SRC address
 * arg4 == flags
 */
#define SMC_RMM_DATA_CREATE			SMC64_RMI_FID(U(0x3))

/*
 * arg0 == data address
 * arg1 == RD address
 * arg2 == map address
 */
#define SMC_RMM_DATA_CREATE_UNKNOWN		SMC64_RMI_FID(U(0x4))

/*
 * arg0 == RD address
 * arg1 == map address
 */
#define SMC_RMM_DATA_DESTROY			SMC64_RMI_FID(U(0x5))

/*
 * arg0 == RD address
 */
#define SMC_RMM_REALM_ACTIVATE			SMC64_RMI_FID(U(0x7))

/*
 * arg0 == RD address
 * arg1 == struct rmi_realm_params addr
 */
#define SMC_RMM_REALM_CREATE			SMC64_RMI_FID(U(0x8))

/*
 * arg0 == RD address
 */
#define SMC_RMM_REALM_DESTROY			SMC64_RMI_FID(U(0x9))

/*
 * arg0 == REC address
 * arg1 == RD address
 * arg2 == struct rmm_rec address
 */
#define SMC_RMM_REC_CREATE			SMC64_RMI_FID(U(0xA))

/*
 * arg0 == REC address
 */
#define SMC_RMM_REC_DESTROY			SMC64_RMI_FID(U(0xB))

/*
 * arg0 == rec address
 * arg1 == rec_run address
 */
#define SMC_RMM_REC_ENTER			SMC64_RMI_FID(U(0xC))

/*
 * arg0 == RTT address
 * arg1 == RD address
 * arg2 == map address
 * arg3 == level
 */
#define SMC_RMM_RTT_CREATE			SMC64_RMI_FID(U(0xD))

/*
 * arg0 == RTT address
 * arg1 == RD address
 * arg2 == map address
 * arg3 == level
 */
#define SMC_RMM_RTT_DESTROY			SMC64_RMI_FID(U(0xE))

/*
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 * arg3 == s2tte
 */
#define SMC_RMM_RTT_MAP_UNPROTECTED		SMC64_RMI_FID(U(0xF))

/*
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 * ret1 == level
 * ret2 == s2tte type
 * ret3 == s2tte
 * ret4 == ripas
 */
#define SMC_RMM_RTT_READ_ENTRY			SMC64_RMI_FID(U(0x11))

/*
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 */
#define SMC_RMM_RTT_UNMAP_UNPROTECTED		SMC64_RMI_FID(U(0x12))

/*
 * arg0 == calling rec address
 * arg1 == target rec address
 */
#define SMC_RMM_PSCI_COMPLETE			SMC64_RMI_FID(U(0x14))

/*
 * arg0 == Feature register index
 */
#define SMC_RMM_FEATURES			SMC64_RMI_FID(U(0x15))

/*
 * arg0 == RTT address
 * arg1 == RD address
 * arg2 == map address
 * arg3 == level
 */
#define SMC_RMM_RTT_FOLD			SMC64_RMI_FID(U(0x16))

/*
 * arg0 == RD address
 */
#define SMC_RMM_REC_AUX_COUNT			SMC64_RMI_FID(U(0x17))

/*
 * arg1 == RD address
 * arg2 == map address
 * arg3 == level
 */
#define SMC_RMM_RTT_INIT_RIPAS			SMC64_RMI_FID(U(0x18))

/*
 * arg0 == RD address
 * arg1 == REC address
 * arg2 == map address
 * arg3 == level
 * arg4 == ripas
 */
#define SMC_RMM_RTT_SET_RIPAS			SMC64_RMI_FID(U(0x19))

/* Size of Realm Personalization Value */
#define RPV_SIZE		64

/*
 * The Realm attribute parameters are shared by the Host via
 * RMI_REALM_CREATE::params_ptr. The values can be observed or modified
 * either by the Host or by the Realm.
 */
struct rmi_realm_params {
	/* Realm feature register 0 */
	SET_MEMBER(unsigned long features_0, 0, 0x100);		/* Offset 0 */
	/* Measurement algorithm */
	SET_MEMBER(unsigned char hash_algo, 0x100, 0x400);	/* 0x100 */
	/* Realm Personalization Value */
	SET_MEMBER(unsigned char rpv[RPV_SIZE], 0x400, 0x800);	/* 0x400 */
	SET_MEMBER(struct {
			/* Virtual Machine Identifier */
			unsigned short vmid;			/* 0x800 */
			/* Realm Translation Table base */
			unsigned long rtt_base;			/* 0x808 */
			/* RTT starting level */
			long rtt_level_start;			/* 0x810 */
			/* Number of starting level RTTs */
			unsigned int rtt_num_start;		/* 0x818 */
		   }, 0x800, 0x1000);
};

COMPILER_ASSERT(sizeof(struct rmi_realm_params) == 0x1000);

COMPILER_ASSERT(offsetof(struct rmi_realm_params, features_0) == 0);
COMPILER_ASSERT(offsetof(struct rmi_realm_params, hash_algo) == 0x100);
COMPILER_ASSERT(offsetof(struct rmi_realm_params, rpv) == 0x400);
COMPILER_ASSERT(offsetof(struct rmi_realm_params, vmid) == 0x800);
COMPILER_ASSERT(offsetof(struct rmi_realm_params, rtt_base) == 0x808);
COMPILER_ASSERT(offsetof(struct rmi_realm_params, rtt_level_start) == 0x810);
COMPILER_ASSERT(offsetof(struct rmi_realm_params, rtt_num_start) == 0x818);

/*
 * The REC attribute parameters are shared by the Host via
 * MI_REC_CREATE::params_ptr. The values can be observed or modified
 * either by the Host or by the Realm which owns the REC.
 */
struct rmi_rec_params {
	/* Flags */
	SET_MEMBER(unsigned long flags, 0, 0x100);	/* Offset 0 */
	/* MPIDR of the REC */
	SET_MEMBER(unsigned long mpidr, 0x100, 0x200);	/* 0x100 */
	/* Program counter */
	SET_MEMBER(unsigned long pc, 0x200, 0x300);	/* 0x200 */
	/* General-purpose registers */
	SET_MEMBER(unsigned long gprs[REC_CREATE_NR_GPRS], 0x300, 0x800); /* 0x300 */
	SET_MEMBER(struct {
			/* Number of auxiliary Granules */
			unsigned long num_aux;			/* 0x800 */
			/* Addresses of auxiliary Granules */
			unsigned long aux[MAX_REC_AUX_GRANULES];/* 0x808 */
		   }, 0x800, 0x1000);
};

COMPILER_ASSERT(sizeof(struct rmi_rec_params) == 0x1000);

COMPILER_ASSERT(offsetof(struct rmi_rec_params, flags) == 0);
COMPILER_ASSERT(offsetof(struct rmi_rec_params, mpidr) == 0x100);
COMPILER_ASSERT(offsetof(struct rmi_rec_params, pc) == 0x200);
COMPILER_ASSERT(offsetof(struct rmi_rec_params, gprs) == 0x300);
COMPILER_ASSERT(offsetof(struct rmi_rec_params, num_aux) == 0x800);
COMPILER_ASSERT(offsetof(struct rmi_rec_params, aux) == 0x808);

/*
 * Structure contains data passed from the Host to the RMM on REC entry
 */
struct rmi_rec_entry {
	/* Flags */
	SET_MEMBER(unsigned long flags, 0, 0x200);	/* Offset 0 */
	/* General-purpose registers */
	SET_MEMBER(unsigned long gprs[REC_EXIT_NR_GPRS], 0x200, 0x300); /* 0x200 */
	SET_MEMBER(struct {
			/* GICv3 Hypervisor Control Register */
			unsigned long gicv3_hcr;			/* 0x300 */
			/* GICv3 List Registers */
			unsigned long gicv3_lrs[REC_GIC_NUM_LRS];	/* 0x308 */
		   }, 0x300, 0x800);
};

COMPILER_ASSERT(sizeof(struct rmi_rec_entry) == 0x800);

COMPILER_ASSERT(offsetof(struct rmi_rec_entry, flags) == 0);
COMPILER_ASSERT(offsetof(struct rmi_rec_entry, gprs) == 0x200);
COMPILER_ASSERT(offsetof(struct rmi_rec_entry, gicv3_hcr) == 0x300);
COMPILER_ASSERT(offsetof(struct rmi_rec_entry, gicv3_lrs) == 0x308);

/*
 * Structure contains data passed from the RMM to the Host on REC exit
 */
struct rmi_rec_exit {
	/* Exit reason */
	SET_MEMBER(unsigned long exit_reason, 0, 0x100);/* Offset 0 */
	SET_MEMBER(struct {
			/* Exception Syndrome Register */
			unsigned long esr;		/* 0x100 */
			/* Fault Address Register */
			unsigned long far;		/* 0x108 */
			/* Hypervisor IPA Fault Address register */
			unsigned long hpfar;		/* 0x110 */
		   }, 0x100, 0x200);
	/* General-purpose registers */
	SET_MEMBER(unsigned long gprs[REC_EXIT_NR_GPRS], 0x200, 0x300); /* 0x200 */
	SET_MEMBER(struct {
			/* GICv3 Hypervisor Control Register */
			unsigned long gicv3_hcr;	/* 0x300 */
			/* GICv3 List Registers */
			unsigned long gicv3_lrs[REC_GIC_NUM_LRS]; /* 0x308 */
			/* GICv3 Maintenance Interrupt State Register */
			unsigned long gicv3_misr;	/* 0x388 */
			/* GICv3 Virtual Machine Control Register */
			unsigned long gicv3_vmcr;	/* 0x390 */
		   }, 0x300, 0x400);
	SET_MEMBER(struct {
			/* Counter-timer Physical Timer Control Register */
			unsigned long cntp_ctl;		/* 0x400 */
			/* Counter-timer Physical Timer CompareValue Register */
			unsigned long cntp_cval;	/* 0x408 */
			/* Counter-timer Virtual Timer Control Register */
			unsigned long cntv_ctl;		/* 0x410 */
			/* Counter-timer Virtual Timer CompareValue Register */
			unsigned long cntv_cval;	/* 0x418 */
		   }, 0x400, 0x500);
	SET_MEMBER(struct {
			/* Base address of pending RIPAS change */
			unsigned long ripas_base;	/* 0x500 */
			/* Size of pending RIPAS change */
			unsigned long ripas_size;	/* 0x508 */
			/* RIPAS value of pending RIPAS change */
			unsigned char ripas_value;	/* 0x510 */
		   }, 0x500, 0x600);
	/* Host call immediate value */
	SET_MEMBER(unsigned int imm, 0x600, 0x800);	/* 0x600 */
};

COMPILER_ASSERT(sizeof(struct rmi_rec_exit) == 0x800);

COMPILER_ASSERT(offsetof(struct rmi_rec_exit, exit_reason) == 0);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, esr) == 0x100);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, far) == 0x108);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, hpfar) == 0x110);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, gprs) == 0x200);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, gicv3_hcr) == 0x300);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, gicv3_lrs) == 0x308);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, gicv3_misr) == 0x388);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, gicv3_vmcr) == 0x390);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, cntp_ctl) == 0x400);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, cntp_cval) == 0x408);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, cntv_ctl) == 0x410);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, cntv_cval) == 0x418);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, ripas_base) == 0x500);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, ripas_size) == 0x508);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, ripas_value) == 0x510);
COMPILER_ASSERT(offsetof(struct rmi_rec_exit, imm) == 0x600);

/*
 * Structure contains shared information between RMM and Host
 * during REC entry and REC exit.
 */
struct rmi_rec_run {
	/* Entry information */
	SET_MEMBER(struct rmi_rec_entry entry, 0, 0x800);	/* Offset 0 */
	/* Exit information */
	SET_MEMBER(struct rmi_rec_exit exit, 0x800, 0x1000);	/* 0x800 */
};

COMPILER_ASSERT(sizeof(struct rmi_rec_run) <= GRANULE_SIZE);

COMPILER_ASSERT(offsetof(struct rmi_rec_run, entry) == 0);
COMPILER_ASSERT(offsetof(struct rmi_rec_run, exit) == 0x800);

#endif /* SMC_RMI_H */

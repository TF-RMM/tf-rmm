/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SMC_RMI_H
#define SMC_RMI_H

#include <smc.h>

/*
 * This file describes the Realm Management Interface (RMI) Application Binary
 * Interface (ABI) for SMC calls made from Non-secure state to the RMM and
 * serviced by the RMM.
 */

/*
 * The major version number of the RMI implementation.  Increase this whenever
 * the binary format or semantics of the SMC calls change.
 */
#define RMI_ABI_VERSION_MAJOR		U(66)

/*
 * The minor version number of the RMI implementation.  Increase this when
 * a bug is fixed, or a feature is added without breaking binary compatibility.
 */
#define RMI_ABI_VERSION_MINOR		U(0)

#define RMI_ABI_VERSION			((RMI_ABI_VERSION_MAJOR << U(16)) | \
					RMI_ABI_VERSION_MINOR)

#define RMI_ABI_VERSION_GET_MAJOR(_version) ((_version) >> U(16))
#define RMI_ABI_VERSION_GET_MINOR(_version) ((_version) & U(0xFFFF))

#define SMC64_RMI_FID(_offset)		SMC64_STD_FID(RMI, _offset)

#define IS_SMC64_RMI_FID(_fid)		IS_SMC64_STD_FAST_IN_RANGE(RMI, _fid)

/* Command completed successfully. index is zero. */
#define RMI_SUCCESS			U(0)

/*
 * The value of a command input value caused the command to fail.
 * Index is zero.
 */
#define RMI_ERROR_INPUT			U(1)

/*
 * An attribute of a Realm does not match the expected value.
 * index varies between usages.
 */
#define RMI_ERROR_REALM			U(2)

/*
 * An attribute of a REC does not match the expected value.
 * Index is zero.
 */
#define RMI_ERROR_REC			U(3)

/*
 * An RTT walk terminated before reaching the target RTT level, or reached
 * an RTTE with an unexpected value. index: RTT level at which the walk
 * terminated
 */
#define RMI_ERROR_RTT			U(4)

/*
 * Number of RMI Status Errors.
 */
#define RMI_ERROR_COUNT			U(5)

/*
 * The number of GPRs (starting from X0) that are
 * configured by the host when a REC is created.
 */
#define REC_CREATE_NR_GPRS		U(8)

#define REC_PARAMS_FLAG_RUNNABLE	(UL(1) << 0)

/*
 * The number of GPRs (starting from X0) per voluntary exit context.
 * Per SMCCC.
 */
#define REC_EXIT_NR_GPRS		U(31)

/* RmiHashAlgorithm type */
#define RMI_HASH_SHA_256		U(0)
#define RMI_HASH_SHA_512		U(1)

/* Maximum number of Interrupt Controller List Registers */
#define REC_GIC_NUM_LRS			U(16)

/* Maximum number of auxiliary granules required for a REC */
#define MAX_REC_AUX_GRANULES		U(16)

#define REC_ENTRY_FLAG_EMUL_MMIO	(UL(1) << 0)
#define REC_ENTRY_FLAG_INJECT_SEA	(UL(1) << 1)

/* Flags to specify if WFI/WFE should be trapped to host */
#define REC_ENTRY_FLAG_TRAP_WFI		(UL(1) << 2)
#define REC_ENTRY_FLAG_TRAP_WFE		(UL(1) << 3)

/*
 * RmiRecExitReason represents the reason for a REC exit.
 * This is returned to NS hosts via RMI_REC_ENTER::run_ptr.
 */
#define RMI_EXIT_SYNC			U(0)
#define RMI_EXIT_IRQ			U(1)
#define RMI_EXIT_FIQ			U(2)
#define RMI_EXIT_PSCI			U(3)
#define RMI_EXIT_RIPAS_CHANGE		U(4)
#define RMI_EXIT_HOST_CALL		U(5)
#define RMI_EXIT_SERROR			U(6)

/* RmiRttEntryState represents the state of an RTTE */
#define RMI_UNASSIGNED		UL(0)
#define RMI_ASSIGNED		UL(1)
#define RMI_TABLE		UL(2)

/* RmiFeature enumerations */
#define RMI_FEATURE_FALSE	UL(0)
#define RMI_FEATURE_TRUE	UL(1)

/* RmiFeatureRegister0 format */
#define RMM_FEATURE_REGISTER_0_INDEX		UL(0)

#define RMM_FEATURE_REGISTER_0_S2SZ_SHIFT	UL(0)
#define RMM_FEATURE_REGISTER_0_S2SZ_WIDTH	UL(8)

#define RMM_FEATURE_REGISTER_0_LPA2_SHIFT	UL(8)
#define RMM_FEATURE_REGISTER_0_LPA2_WIDTH	UL(1)

#define RMM_FEATURE_REGISTER_0_SVE_EN_SHIFT	UL(9)
#define RMM_FEATURE_REGISTER_0_SVE_EN_WIDTH	UL(1)

#define RMM_FEATURE_REGISTER_0_SVE_VL_SHIFT	UL(10)
#define RMM_FEATURE_REGISTER_0_SVE_VL_WIDTH	UL(4)

#define RMM_FEATURE_REGISTER_0_NUM_BPS_SHIFT	UL(14)
#define RMM_FEATURE_REGISTER_0_NUM_BPS_WIDTH	UL(4)

#define RMM_FEATURE_REGISTER_0_NUM_WPS_SHIFT	UL(18)
#define RMM_FEATURE_REGISTER_0_NUM_WPS_WIDTH	UL(4)

#define RMM_FEATURE_REGISTER_0_PMU_EN_SHIFT	UL(22)
#define RMM_FEATURE_REGISTER_0_PMU_EN_WIDTH	UL(1)

#define RMM_FEATURE_REGISTER_0_PMU_NUM_CTRS_SHIFT	UL(23)
#define RMM_FEATURE_REGISTER_0_PMU_NUM_CTRS_WIDTH	UL(5)

#define RMM_FEATURE_REGISTER_0_HASH_SHA_256_SHIFT	UL(28)
#define RMM_FEATURE_REGISTER_0_HASH_SHA_256_WIDTH	UL(1)

#define RMM_FEATURE_REGISTER_0_HASH_SHA_512_SHIFT	UL(29)
#define RMM_FEATURE_REGISTER_0_HASH_SHA_512_WIDTH	UL(1)

/* The RmiRipas enumeration represents realm IPA state */

/* Address where no Realm resources are mapped */
#define RMI_EMPTY	UL(0)

/* Address where private code or data owned by the Realm is mapped */
#define RMI_RAM		UL(1)

/* Address which is inaccessible to the Realm due to an action taken by the Host */
#define RMI_DESTROYED	UL(2)

/* RmiPmuOverflowStatus enumeration representing PMU overflow status */
#define RMI_PMU_OVERFLOW_NOT_ACTIVE	U(0)
#define RMI_PMU_OVERFLOW_ACTIVE		U(1)

/* No parameters */
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
#define RMI_NO_MEASURE_CONTENT	U(0)
#define RMI_MEASURE_CONTENT	U(1)

/*
 * arg0 == RD address
 * arg1 == data address
 * arg2 == map address
 * arg3 == SRC address
 * arg4 == flags
 */
#define SMC_RMM_DATA_CREATE			SMC64_RMI_FID(U(0x3))

/*
 * arg0 == RD address
 * arg1 == data address
 * arg2 == map address
 */
#define SMC_RMM_DATA_CREATE_UNKNOWN		SMC64_RMI_FID(U(0x4))

/*
 * arg0 == RD address
 * arg1 == map address
 *
 * ret1 == Address(PA) of the DATA granule, if ret0 == RMI_SUCCESS.
 *         Otherwise, undefined.
 * ret2 == Top of the non-live address region. Only valid
 *         if ret0 == RMI_SUCCESS or ret0 == (RMI_ERROR_RTT, x)
 */
#define SMC_RMM_DATA_DESTROY			SMC64_RMI_FID(U(0x5))

/*
 * arg0 == RD address
 */
#define SMC_RMM_REALM_ACTIVATE			SMC64_RMI_FID(U(0x7))

/*
 * arg0 == RD address
 * arg1 == struct rmi_realm_params address
 */
#define SMC_RMM_REALM_CREATE			SMC64_RMI_FID(U(0x8))

/*
 * arg0 == RD address
 */
#define SMC_RMM_REALM_DESTROY			SMC64_RMI_FID(U(0x9))

/*
 * arg0 == RD address
 * arg1 == REC address
 * arg2 == struct rmm_rec address
 */
#define SMC_RMM_REC_CREATE			SMC64_RMI_FID(U(0xA))

/*
 * arg0 == REC address
 */
#define SMC_RMM_REC_DESTROY			SMC64_RMI_FID(U(0xB))

/*
 * arg0 == rec address
 * arg1 == struct rec_run address
 */
#define SMC_RMM_REC_ENTER			SMC64_RMI_FID(U(0xC))

/*
 * arg0 == RD address
 * arg1 == RTT address
 * arg2 == map address
 * arg3 == level
 */
#define SMC_RMM_RTT_CREATE			SMC64_RMI_FID(U(0xD))

/*
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 *
 * ret1 == Address (PA) of the RTT, if ret0 == RMI_SUCCESS
 *         Otherwise, undefined.
 * ret2 == Top of the non-live address region. Only valid
 *         if ret0 == RMI_SUCCESS or ret0 == (RMI_ERROR_RTT, x)
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
 *
 * ret1 == level
 * ret2 == s2tte type
 * ret3 == s2tte
 * ret4 == ripas
 * if ret0 == RMI_SUCCESS, otherwise, undefined.
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
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 *
 * ret1 == Address(PA) of the RTT folded, if ret0 == RMI_SUCCESS
 */
#define SMC_RMM_RTT_FOLD			SMC64_RMI_FID(U(0x16))

/*
 * arg0 == RD address
 */
#define SMC_RMM_REC_AUX_COUNT			SMC64_RMI_FID(U(0x17))

/*
 * arg0 == RD address
 * arg1 == start address
 * arg2 == end address
 *
 * ret1 == Top of the address range where the RIPAS was updated,
 * if ret0 == RMI_SUCCESS
 */
#define SMC_RMM_RTT_INIT_RIPAS			SMC64_RMI_FID(U(0x18))

/*
 * arg0 == RD address
 * arg1 == REC address
 * arg2 == start address
 * arg3 == end address
 *
 * ret1 == Top of the address range where the RIPAS was updated,
 *	   if ret0 == RMI_SUCCESS
 */
#define SMC_RMM_RTT_SET_RIPAS			SMC64_RMI_FID(U(0x19))

/* Size of Realm Personalization Value */
#define RPV_SIZE		64

/* RmiRealmFlags format */
#define RMI_REALM_FLAGS_LPA2_SHIFT	UL(0)
#define RMI_REALM_FLAGS_LPA2_WIDTH	UL(1)

#define RMI_REALM_FLAGS_SVE_SHIFT	UL(1)
#define RMI_REALM_FLAGS_SVE_WIDTH	UL(1)

#define RMI_REALM_FLAGS_PMU_SHIFT	UL(2)
#define RMI_REALM_FLAGS_PMU_WIDTH	UL(1)

#ifndef __ASSEMBLER__
/*
 * Defines member of structure and reserves space
 * for the next member with specified offset.
 */
#define SET_MEMBER_RMI	SET_MEMBER

/*
 * The Realm attribute parameters are shared by the Host via
 * RMI_REALM_CREATE::params_ptr. The values can be observed or modified
 * either by the Host or by the Realm.
 */
struct rmi_realm_params {
	/* Flags */
	SET_MEMBER_RMI(unsigned long flags, 0, 0x8);		/* Offset 0 */
	/* Requested IPA width */
	SET_MEMBER_RMI(unsigned int s2sz, 0x8, 0x10);		/* 0x8 */
	/* Requested SVE vector length */
	SET_MEMBER_RMI(unsigned int sve_vl, 0x10, 0x18);	/* 0x10 */
	/* Requested number of breakpoints */
	SET_MEMBER_RMI(unsigned int num_bps, 0x18, 0x20);	/* 0x18 */
	/* Requested number of watchpoints */
	SET_MEMBER_RMI(unsigned int num_wps, 0x20, 0x28);	/* 0x20 */
	/* Requested number of PMU counters */
	SET_MEMBER_RMI(unsigned int pmu_num_ctrs, 0x28, 0x30);	/* 0x28 */
	/* Measurement algorithm */
	SET_MEMBER_RMI(unsigned char hash_algo, 0x30, 0x400);	/* 0x30 */
	/* Realm Personalization Value */
	SET_MEMBER_RMI(unsigned char rpv[RPV_SIZE], 0x400, 0x800); /* 0x400 */
	SET_MEMBER_RMI(struct {
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

/*
 * The REC attribute parameters are shared by the Host via
 * MI_REC_CREATE::params_ptr. The values can be observed or modified
 * either by the Host or by the Realm which owns the REC.
 */
struct rmi_rec_params {
	/* Flags */
	SET_MEMBER_RMI(unsigned long flags, 0, 0x100);	/* Offset 0 */
	/* MPIDR of the REC */
	SET_MEMBER_RMI(unsigned long mpidr, 0x100, 0x200);	/* 0x100 */
	/* Program counter */
	SET_MEMBER_RMI(unsigned long pc, 0x200, 0x300);	/* 0x200 */
	/* General-purpose registers */
	SET_MEMBER_RMI(unsigned long gprs[REC_CREATE_NR_GPRS], 0x300, 0x800); /* 0x300 */
	SET_MEMBER_RMI(struct {
			/* Number of auxiliary Granules */
			unsigned long num_aux;			/* 0x800 */
			/* Addresses of auxiliary Granules */
			unsigned long aux[MAX_REC_AUX_GRANULES];/* 0x808 */
		   }, 0x800, 0x1000);
};

/*
 * Structure contains data passed from the Host to the RMM on REC entry
 */
struct rmi_rec_entry {
	/* Flags */
	SET_MEMBER_RMI(unsigned long flags, 0, 0x200);	/* Offset 0 */
	/* General-purpose registers */
	SET_MEMBER_RMI(unsigned long gprs[REC_EXIT_NR_GPRS], 0x200, 0x300); /* 0x200 */
	SET_MEMBER_RMI(struct {
			/* GICv3 Hypervisor Control Register */
			unsigned long gicv3_hcr;			/* 0x300 */
			/* GICv3 List Registers */
			unsigned long gicv3_lrs[REC_GIC_NUM_LRS];	/* 0x308 */
		   }, 0x300, 0x800);
};

/*
 * Structure contains data passed from the RMM to the Host on REC exit
 */
struct rmi_rec_exit {
	/* Exit reason */
	SET_MEMBER_RMI(unsigned long exit_reason, 0, 0x100);/* Offset 0 */
	SET_MEMBER_RMI(struct {
			/* Exception Syndrome Register */
			unsigned long esr;		/* 0x100 */
			/* Fault Address Register */
			unsigned long far;		/* 0x108 */
			/* Hypervisor IPA Fault Address register */
			unsigned long hpfar;		/* 0x110 */
		   }, 0x100, 0x200);
	/* General-purpose registers */
	SET_MEMBER_RMI(unsigned long gprs[REC_EXIT_NR_GPRS], 0x200, 0x300); /* 0x200 */
	SET_MEMBER_RMI(struct {
			/* GICv3 Hypervisor Control Register */
			unsigned long gicv3_hcr;	/* 0x300 */
			/* GICv3 List Registers */
			unsigned long gicv3_lrs[REC_GIC_NUM_LRS]; /* 0x308 */
			/* GICv3 Maintenance Interrupt State Register */
			unsigned long gicv3_misr;	/* 0x388 */
			/* GICv3 Virtual Machine Control Register */
			unsigned long gicv3_vmcr;	/* 0x390 */
		   }, 0x300, 0x400);
	SET_MEMBER_RMI(struct {
			/* Counter-timer Physical Timer Control Register */
			unsigned long cntp_ctl;		/* 0x400 */
			/* Counter-timer Physical Timer CompareValue Register */
			unsigned long cntp_cval;	/* 0x408 */
			/* Counter-timer Virtual Timer Control Register */
			unsigned long cntv_ctl;		/* 0x410 */
			/* Counter-timer Virtual Timer CompareValue Register */
			unsigned long cntv_cval;	/* 0x418 */
		   }, 0x400, 0x500);
	SET_MEMBER_RMI(struct {
			/* Base address of pending RIPAS change */
			unsigned long ripas_base;	/* 0x500 */
			/* Size of pending RIPAS change */
			unsigned long ripas_top;	/* 0x508 */
			/* RIPAS value of pending RIPAS change */
			unsigned char ripas_value;	/* 0x510 */
		   }, 0x500, 0x600);
	/* Host call immediate value */
	SET_MEMBER_RMI(unsigned int imm, 0x600, 0x700);	/* 0x600 */
	/* PMU overflow status */
	SET_MEMBER_RMI(unsigned long pmu_ovf_status, 0x700, 0x800);	/* 0x700 */
};

/*
 * Structure contains shared information between RMM and Host
 * during REC entry and REC exit.
 */
struct rmi_rec_run {
	/* Entry information */
	SET_MEMBER_RMI(struct rmi_rec_entry entry, 0, 0x800);	/* Offset 0 */
	/* Exit information */
	SET_MEMBER_RMI(struct rmi_rec_exit exit, 0x800, 0x1000);/* 0x800 */
};

#endif /* __ASSEMBLER__ */

#endif /* SMC_RMI_H */

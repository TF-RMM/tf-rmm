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
#define RMI_ABI_VERSION_MAJOR		UL(1)

/*
 * The minor version number of the RMI implementation.  Increase this when
 * a bug is fixed, or a feature is added without breaking binary compatibility.
 */
#ifdef RMM_V1_1
#define RMI_ABI_VERSION_MINOR		UL(1)
#else
#define RMI_ABI_VERSION_MINOR		UL(0)
#endif

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

/* An attribute of a device does not match the expected value */
#define RMI_ERROR_DEVICE		U(5)

/* The command is not supported */
#define RMI_ERROR_NOT_SUPPORTED		U(6)

/* RTTE in an auxiliary RTT contained an unexpected value */
#define RMI_ERROR_RTT_AUX		U(7)

/* Max number of RMI Status Errors. */
#define RMI_ERROR_COUNT_MAX		U(8)

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
#define RMI_HASH_SHA_256		0U
#define RMI_HASH_SHA_512		1U

/* Maximum number of Interrupt Controller List Registers */
#define REC_GIC_NUM_LRS			U(16)

#ifndef CBMC
/* Maximum number of auxiliary granules required for a REC */
#define MAX_REC_AUX_GRANULES		U(16)
#else /* CBMC */
#define MAX_REC_AUX_GRANULES		U(1)
#endif /* CBMC */

/* Whether Host has completed emulation for an Emulatable Data Abort */
#define REC_ENTRY_FLAG_EMUL_MMIO	(UL(1) << 0)

/* Whether to inject a Synchronous External Abort into Realm */
#define REC_ENTRY_FLAG_INJECT_SEA	(UL(1) << 1)

/* Whether to trap WFI/WFE execution by Realm */
#define REC_ENTRY_FLAG_TRAP_WFI		(UL(1) << 2)
#define REC_ENTRY_FLAG_TRAP_WFE		(UL(1) << 3)

/* Host response to RIPAS change request */
#define REC_ENTRY_FLAG_RIPAS_RESPONSE	(UL(1) << 4)

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
#define RMI_EXIT_DEV_COMM		U(7)
#define RMI_EXIT_RTT_REQUEST		U(8)
#define RMI_EXIT_S2AP_CHANGE		U(9)
#define RMI_EXIT_VDEV_REQUEST		U(10)

/* RmiRttEntryState represents the state of an RTTE */
#define RMI_UNASSIGNED		UL(0)
#define RMI_ASSIGNED		UL(1)
#define RMI_TABLE		UL(2)

/* RmiFeature enumerations */
#define RMI_FEATURE_FALSE	UL(0)
#define RMI_FEATURE_TRUE	UL(1)

/* RmiFeatureRegister0 format */
#define RMI_FEATURE_REGISTER_0_INDEX			UL(0)

#define RMI_FEATURE_REGISTER_0_S2SZ_SHIFT		UL(0)
#define RMI_FEATURE_REGISTER_0_S2SZ_WIDTH		UL(8)

#define RMI_FEATURE_REGISTER_0_LPA2_SHIFT		UL(8)
#define RMI_FEATURE_REGISTER_0_LPA2_WIDTH		UL(1)

#define RMI_FEATURE_REGISTER_0_SVE_EN_SHIFT		UL(9)
#define RMI_FEATURE_REGISTER_0_SVE_EN_WIDTH		UL(1)

#define RMI_FEATURE_REGISTER_0_SVE_VL_SHIFT		UL(10)
#define RMI_FEATURE_REGISTER_0_SVE_VL_WIDTH		UL(4)

#define RMI_FEATURE_REGISTER_0_NUM_BPS_SHIFT		UL(14)
#define RMI_FEATURE_REGISTER_0_NUM_BPS_WIDTH		UL(6)

#define RMI_FEATURE_REGISTER_0_NUM_WPS_SHIFT		UL(20)
#define RMI_FEATURE_REGISTER_0_NUM_WPS_WIDTH		UL(6)

#define RMI_FEATURE_REGISTER_0_PMU_EN_SHIFT		UL(26)
#define RMI_FEATURE_REGISTER_0_PMU_EN_WIDTH		UL(1)

#define RMI_FEATURE_REGISTER_0_PMU_NUM_CTRS_SHIFT	UL(27)
#define RMI_FEATURE_REGISTER_0_PMU_NUM_CTRS_WIDTH	UL(5)

#define RMI_FEATURE_REGISTER_0_HASH_SHA_256_SHIFT	UL(32)
#define RMI_FEATURE_REGISTER_0_HASH_SHA_256_WIDTH	UL(1)

#define RMI_FEATURE_REGISTER_0_HASH_SHA_512_SHIFT	UL(33)
#define RMI_FEATURE_REGISTER_0_HASH_SHA_512_WIDTH	UL(1)

#define RMI_FEATURE_REGISTER_0_GICV3_NUM_LRS_SHIFT	UL(34)
#define RMI_FEATURE_REGISTER_0_GICV3_NUM_LRS_WIDTH	UL(4)

#define RMI_FEATURE_REGISTER_0_MAX_RECS_ORDER_SHIFT	UL(38)
#define RMI_FEATURE_REGISTER_0_MAX_RECS_ORDER_WIDTH	UL(4)

#define RMI_FEATURE_REGISTER_0_DA_EN_SHIFT		UL(42)
#define RMI_FEATURE_REGISTER_0_DA_EN_WIDTH		UL(1)

#define RMI_FEATURE_REGISTER_0_PLANE_RTT_SHIFT		UL(43)
#define RMI_FEATURE_REGISTER_0_PLANE_RTT_WIDTH		UL(2)

#define RMI_FEATURE_REGISTER_0_MAX_NUM_AUX_PLANES_SHIFT	UL(45)
#define RMI_FEATURE_REGISTER_0_MAX_NUM_AUX_PLANES_WIDTH	UL(4)

/* The RmiRipas enumeration represents realm IPA state */

/* Address where no Realm resources are mapped */
#define RMI_EMPTY	UL(0)

/* Address where private code or data owned by the Realm is mapped */
#define RMI_RAM		UL(1)

/* Address which is inaccessible to the Realm due to an action taken by the Host */
#define RMI_DESTROYED	UL(2)

/* Address where MMIO of an assigned Realm device is mapped. */
#define RMI_IO		UL(3)

/* RmiPmuOverflowStatus enumeration representing PMU overflow status */
#define RMI_PMU_OVERFLOW_NOT_ACTIVE	U(0)
#define RMI_PMU_OVERFLOW_ACTIVE		U(1)

/*
 * RmiResponse enumeration represents whether the Host accepted
 * or rejected a Realm request
 */
#define RMI_ACCEPT	0U
#define RMI_REJECT	1U

/*
 * FID: 0xC4000150
 *
 * arg0: Requested interface version
 *
 * ret0: Command return status
 * ret1: Lower implemented interface revision
 * ret2: Higher implemented interface revision
 */
#define SMC_RMI_VERSION				SMC64_RMI_FID(U(0x0))

/*
 * FID: 0xC4000151
 *
 * arg0 == target granule address
 */
#define SMC_RMI_GRANULE_DELEGATE		SMC64_RMI_FID(U(0x1))

/*
 * FID: 0xC4000152
 *
 * arg0 == target granule address
 */
#define SMC_RMI_GRANULE_UNDELEGATE		SMC64_RMI_FID(U(0x2))

/* RmiDataMeasureContent type */
#define RMI_NO_MEASURE_CONTENT	U(0)
#define RMI_MEASURE_CONTENT	U(1)

/*
 * FID: 0xC4000153
 *
 * arg0 == RD address
 * arg1 == data address
 * arg2 == map address
 * arg3 == SRC address
 * arg4 == flags
 */
#define SMC_RMI_DATA_CREATE			SMC64_RMI_FID(U(0x3))

/*
 * FID: 0xC4000154
 *
 * arg0 == RD address
 * arg1 == data address
 * arg2 == map address
 */
#define SMC_RMI_DATA_CREATE_UNKNOWN		SMC64_RMI_FID(U(0x4))

/*
 * FID: 0xC4000155
 *
 * arg0 == RD address
 * arg1 == map address
 *
 * ret1 == Address(PA) of the DATA granule, if ret0 == RMI_SUCCESS.
 *         Otherwise, undefined.
 * ret2 == Top of the non-live address region. Only valid
 *         if ret0 == RMI_SUCCESS or ret0 == (RMI_ERROR_RTT, x)
 */
#define SMC_RMI_DATA_DESTROY			SMC64_RMI_FID(U(0x5))

/*
 * FID: 0xC4000156
 */
#define SMC_RMI_PDEV_AUX_COUNT			SMC64_RMI_FID(U(0x6))

/*
 * FID: 0xC4000157
 *
 * arg0 == RD address
 */
#define SMC_RMI_REALM_ACTIVATE			SMC64_RMI_FID(U(0x7))

/*
 * FID: 0xC4000158
 *
 * arg0 == RD address
 * arg1 == struct rmi_realm_params address
 */
#define SMC_RMI_REALM_CREATE			SMC64_RMI_FID(U(0x8))

/*
 * FID: 0xC4000159
 *
 * arg0 == RD address
 */
#define SMC_RMI_REALM_DESTROY			SMC64_RMI_FID(U(0x9))

/*
 * FID: 0xC400015A
 *
 * arg0 == RD address
 * arg1 == REC address
 * arg2 == struct rmm_rec address
 */
#define SMC_RMI_REC_CREATE			SMC64_RMI_FID(U(0xA))

/*
 * FID: 0xC400015B
 *
 * arg0 == REC address
 */
#define SMC_RMI_REC_DESTROY			SMC64_RMI_FID(U(0xB))

/*
 * FID: 0xC400015C
 *
 * arg0 == rec address
 * arg1 == struct rec_run address
 */
#define SMC_RMI_REC_ENTER			SMC64_RMI_FID(U(0xC))

/*
 * FID: 0xC400015D
 *
 * arg0 == RD address
 * arg1 == RTT address
 * arg2 == map address
 * arg3 == level
 */
#define SMC_RMI_RTT_CREATE			SMC64_RMI_FID(U(0xD))

/*
 * FID: 0xC400015E
 *
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 *
 * ret1 == Address (PA) of the RTT, if ret0 == RMI_SUCCESS
 *         Otherwise, undefined.
 * ret2 == Top of the non-live address region. Only valid
 *         if ret0 == RMI_SUCCESS or ret0 == (RMI_ERROR_RTT, x)
 */
#define SMC_RMI_RTT_DESTROY			SMC64_RMI_FID(U(0xE))

/*
 * FID: 0xC400015F
 *
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 * arg3 == s2tte
 */
#define SMC_RMI_RTT_MAP_UNPROTECTED		SMC64_RMI_FID(U(0xF))

/*
 * FID: 0xC4000160
 */
#define SMC_RMI_VDEV_AUX_COUNT			SMC64_RMI_FID(U(0x10))

/*
 * FID: 0xC4000161
 *
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
#define SMC_RMI_RTT_READ_ENTRY			SMC64_RMI_FID(U(0x11))

/*
 * FID: 0xC4000162
 *
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 */
#define SMC_RMI_RTT_UNMAP_UNPROTECTED		SMC64_RMI_FID(U(0x12))

/*
 * FID: 0xC4000164
 *
 * arg0 == calling rec address
 * arg1 == target rec address
 */
#define SMC_RMI_PSCI_COMPLETE			SMC64_RMI_FID(U(0x14))

/*
 * FID: 0xC4000165
 *
 * arg0 == Feature register index
 */
#define SMC_RMI_FEATURES			SMC64_RMI_FID(U(0x15))

/*
 * FID: 0xC4000166
 *
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 *
 * ret1 == Address(PA) of the RTT folded, if ret0 == RMI_SUCCESS
 */
#define SMC_RMI_RTT_FOLD			SMC64_RMI_FID(U(0x16))

/*
 * FID: 0xC4000167
 *
 * arg0 == RD address
 */
#define SMC_RMI_REC_AUX_COUNT			SMC64_RMI_FID(U(0x17))

/*
 * FID: 0xC4000168
 *
 * arg0 == RD address
 * arg1 == start address
 * arg2 == end address
 *
 * ret1 == Top of the address range where the RIPAS was updated,
 * if ret0 == RMI_SUCCESS
 */
#define SMC_RMI_RTT_INIT_RIPAS			SMC64_RMI_FID(U(0x18))

/*
 * FID: 0xC4000169
 *
 * arg0 == RD address
 * arg1 == REC address
 * arg2 == start address
 * arg3 == end address
 *
 * ret1 == Top of the address range where the RIPAS was updated,
 *	   if ret0 == RMI_SUCCESS
 */
#define SMC_RMI_RTT_SET_RIPAS			SMC64_RMI_FID(U(0x19))

/*
 * TODO: Update the documentation of new FIDs once the 1.1 spec has stabilized.
 */

/*
 * FID: 0xC4000170
 */
#define SMC_RMI_GRANULE_DEV_DELEGATE		SMC64_RMI_FID(U(0x20))

/*
 * FID: 0xC4000171
 */
#define SMC_RMI_GRANULE_DEV_UNDELEGATE		SMC64_RMI_FID(U(0x21))

/*
 * FID: 0xC4000172
 */
#define SMC_RMI_DEV_MAP				SMC64_RMI_FID(U(0x22))

/*
 * FID: 0xC4000173
 */
#define SMC_RMI_DEV_UNMAP			SMC64_RMI_FID(U(0x23))

/*
 * FID: 0xC4000174
 */
#define SMC_RMI_PDEV_ABORT			SMC64_RMI_FID(U(0x24))

/*
 * FID: 0xC4000175
 */
#define SMC_RMI_PDEV_COMMUNICATE		SMC64_RMI_FID(U(0x25))

/*
 * FID: 0xC4000176
 */
#define SMC_RMI_PDEV_CREATE			SMC64_RMI_FID(U(0x26))

/*
 * FID: 0xC4000177
 */
#define SMC_RMI_PDEV_DESTROY			SMC64_RMI_FID(U(0x27))

/*
 * FID: 0xC4000178
 */
#define SMC_RMI_PDEV_GET_STATE			SMC64_RMI_FID(U(0x28))

/*
 * FID: 0xC4000179
 */
#define SMC_RMI_PDEV_IDE_RESET			SMC64_RMI_FID(U(0x29))

/*
 * FID: 0xC400017A
 */
#define SMC_RMI_PDEV_NOTIFY			SMC64_RMI_FID(U(0x2A))

/*
 * FID: 0xC400017B
 */
#define SMC_RMI_PDEV_SET_PUBKEY			SMC64_RMI_FID(U(0x2B))

/*
 * FID: 0xC400017C
 */
#define SMC_RMI_PDEV_STOP			SMC64_RMI_FID(U(0x2C))

/*
 * FID: 0xC400017D
 */
#define SMC_RMI_RTT_AUX_CREATE			SMC64_RMI_FID(U(0x2D))

/*
 * FID: 0xC400017E
 */
#define SMC_RMI_RTT_AUX_DESTROY			SMC64_RMI_FID(U(0x2E))

/*
 * FID: 0xC400017F
 */
#define SMC_RMI_RTT_AUX_FOLD			SMC64_RMI_FID(U(0x2F))

/*
 * FID: 0xC4000180
 */
#define SMC_RMI_RTT_AUX_MAP_PROTECTED		SMC64_RMI_FID(U(0x30))

/*
 * FID: 0xC4000181
 */
#define SMC_RMI_RTT_AUX_MAP_UNPROTECTED		SMC64_RMI_FID(U(0x31))

/*
 * FID: 0xC4000183
 */
#define SMC_RMI_RTT_AUX_UNMAP_PROTECTED		SMC64_RMI_FID(U(0x33))

/*
 * FID: 0xC4000184
 */
#define SMC_RMI_RTT_AUX_UNMAP_UNPROTECTED	SMC64_RMI_FID(U(0x34))

/*
 * FID: 0xC4000185
 */
#define SMC_RMI_VDEV_ABORT			SMC64_RMI_FID(U(0x35))

/*
 * FID: 0xC4000186
 */
#define SMC_RMI_VDEV_COMMUNICATE		SMC64_RMI_FID(U(0x36))

/*
 * FID: 0xC4000187
 */
#define SMC_RMI_VDEV_CREATE			SMC64_RMI_FID(U(0x37))

/*
 * FID: 0xC4000188
 */
#define SMC_RMI_VDEV_DESTROY			SMC64_RMI_FID(U(0x38))

/*
 * FID: 0xC4000189
 */
#define SMC_RMI_VDEV_GET_STATE			SMC64_RMI_FID(U(0x39))

/*
 * FID: 0xC400018A
 */
#define SMC_RMI_VDEV_STOP			SMC64_RMI_FID(U(0x3A))

/*
 * FID: 0xC400018B
 */
#define SMC_RMI_RTT_SET_S2AP			SMC64_RMI_FID(U(0x3B))

/*
 * FID: 0xC400018C
 */
#define SMC_RMI_MEC_SET_SHARED			SMC64_RMI_FID(U(0x3C))

/*
 * FID: 0xC400018D
 */
#define SMC_RMI_MEC_SET_PRIVATE			SMC64_RMI_FID(U(0x3D))

/*
 * FID: 0xC400018E
 */
#define SMC_RMI_VDEV_COMPLETE			SMC64_RMI_FID(U(0x3E))

/* Size of Realm Personalization Value */
#ifndef CBMC
#define RPV_SIZE		64
#else
/*
 * Small RPV size so that `struct rd` fits in the reduced sized granule defined
 * for CBMC
 */
#define RPV_SIZE		1
#endif

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
	SET_MEMBER_RMI(unsigned char algorithm, 0x30, 0x400);	/* 0x30 */
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
 * RMI_REC_CREATE::params_ptr. The values can be observed or modified
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
struct rmi_rec_enter {
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
 * RmiVdevAction
 * Represents realm action which triggered REC exit due to device communication.
 * Width: 8 bits
 */
#define RMI_VDEV_ACTION_GET_INTERFACE_REPORT	U(0)
#define RMI_VDEV_ACTION_GET_MEASUREMENTS	U(1)
#define RMI_VDEV_ACTION_LOCK			U(2)
#define RMI_VDEV_ACTION_START			U(3)
#define RMI_VDEV_ACTION_STOP			U(4)

/*
 * RmiRecExitFlags
 * Fieldset contains flags provided by the RMM during REC exit.
 * Width: 64 bits
 */
#define RMI_REC_EXIT_FLAGS_RIPAS_DEV_SHARED_SHIFT	U(0)
#define RMI_REC_EXIT_FLAGS_RIPAS_DEV_SHARED_WIDTH	U(1)

/*
 * Structure contains data passed from the RMM to the Host on REC exit
 */
struct rmi_rec_exit {
	/* Exit reason */
	SET_MEMBER_RMI(unsigned long exit_reason, 0, 0x8);/* Offset 0 */
	/* RmiRecExitFlags: Flags */
	SET_MEMBER_RMI(unsigned long flags, 0x8, 0x100);/* 0x8 */
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
			/*
			 * Base PA of device memory region, if RIPAS change is
			 * pending due to execution of
			 * RSI_RDEV_VALIDATE_MAPPING
			 */
			unsigned long ripas_dev_pa; /* 0x518 */
			/* Base addr of target region for pending S2AP change */
			unsigned long s2ap_base; /* 0x520 */
			/* Top addr of target region for pending S2AP change */
			unsigned long s2ap_top; /* 0x528 */
			/* Virtual device ID */
			unsigned long vdev_id; /* 0x530 */
		   }, 0x500, 0x600);
	/* Host call immediate value */
	SET_MEMBER_RMI(unsigned int imm, 0x600, 0x608);	/* 0x600 */
	/* UInt64: Plane Index */
	SET_MEMBER_RMI(unsigned long plane, 0x608, 0x610);	/* 0x608 */
	/* Address: VDEV which triggered REC exit due to device communication */
	SET_MEMBER_RMI(unsigned long vdev, 0x610, 0x618);	/* 0x610 */
	/* RmiVdevAction: Action which triggered REC exit due to device comm */
	SET_MEMBER_RMI(unsigned char vdev_action, 0x618, 0x700); /* 0x618 */
	/* PMU overflow status */
	SET_MEMBER_RMI(unsigned long pmu_ovf_status, 0x700, 0x800);	/* 0x700 */
};

/*
 * Structure contains shared information between RMM and Host
 * during REC entry and REC exit.
 */
struct rmi_rec_run {
	/* Entry information */
	SET_MEMBER_RMI(struct rmi_rec_enter enter, 0, 0x800);	/* Offset 0 */
	/* Exit information */
	SET_MEMBER_RMI(struct rmi_rec_exit exit, 0x800, 0x1000);/* 0x800 */
};

/*
 * RmiPdevProtConfig
 * Represents the protection between system and device.
 * Width: 2 bits
 */
#define RMI_PDEV_IOCOH_E2E_IDE			U(0)
#define RMI_PDEV_IOCOH_E2E_SYS			U(1)
#define RMI_PDEV_FCOH_E2E_IDE			U(2)
#define RMI_PDEV_FCOH_E2E_SYS			U(3)

/*
 * RmiPdevFlags
 * Fieldset contains flags provided by the Host during PDEV creation
 * Width: 64 bits
 */
/* RmiPdevProtConfig Bits 1:0 */
#define RMI_PDEV_FLAGS_PROT_CONFIG_SHIFT	UL(0)
#define RMI_PDEV_FLAGS_PROT_CONFIG_WIDTH	UL(2)

/*
 * RmiPdevEvent
 * Represents physical device event.
 * Width: 8 bits
 */
#define RMI_PDEV_EVENT_IDE_KEY_REFRESH		U(0)

/*
 * RmiPdevState
 * Represents the state of a PDEV
 * Width: 8 bits
 */
#define RMI_PDEV_STATE_NEW			U(0)
#define RMI_PDEV_STATE_NEEDS_KEY		U(1)
#define RMI_PDEV_STATE_HAS_KEY			U(2)
#define RMI_PDEV_STATE_READY			U(3)
#define RMI_PDEV_STATE_COMMUNICATING		U(4)
#define RMI_PDEV_STATE_STOPPING			U(5)
#define RMI_PDEV_STATE_STOPPED			U(6)
#define RMI_PDEV_STATE_ERROR			U(7)

/*
 * RmiSignatureAlgorithm
 * Represents signature algorithm used in PDEV set key RMI call.
 * Width: 8 bits
 */
#define RMI_SIGNATURE_ALGORITHM_RSASSA_3072	U(0)
#define RMI_SIGNATURE_ALGORITHM_ECDSA_P256	U(1)
#define RMI_SIGNATURE_ALGORITHM_ECDSA_P384	U(2)

/*
 * RmiDevMemShared
 * Represents whether device memory Granule should be shared
 * Width: 1 bit
 */
#define RMI_DEV_MEM_PRIVATE			U(0)
#define RMI_DEV_MEM_SHARED			U(1)

/*
 * RmiDevDelegateFlags
 * Fieldset contains flags provided by the Host during device memory granule
 * delegation.
 * Width: 64 bits
 */
/* RmiDevMemShared: Bit 0 */
#define RMI_DEV_DELEGATE_FLAGS_SHARE_SHIFT	U(0)
#define RMI_DEV_DELEGATE_FLAGS_SHARE_WIDTH	U(1)

/*
 * RmiDevCommEnterStatus (Name in Spec RmiDevCommStatus)
 * Represents status passed from the Host to the RMM during device communication.
 * Width: 8 bits
 */
#define RMI_DEV_COMM_ENTER_STATUS_SUCCESS	U(0)
#define RMI_DEV_COMM_ENTER_STATUS_ERROR		U(1)
#define RMI_DEV_COMM_ENTER_STATUS_NONE		U(2)

/*
 * RmiDevCommEnter
 * This structure contains data passed from the Host to the RMM during device
 * communication.
 * Width: 256 (0x100) bytes
 */
struct rmi_dev_comm_enter {
	/* RmiDevCommEnterStatus: Status of device transaction */
	SET_MEMBER_RMI(unsigned char status, 0, 0x8);
	/* Address: Address of request buffer */
	SET_MEMBER_RMI(unsigned long req_addr, 0x8, 0x10);
	/* Address: Address of response buffer */
	SET_MEMBER_RMI(unsigned long resp_addr, 0x10, 0x18);
	/* UInt64: Amount of valid data in response buffer in bytes */
	SET_MEMBER_RMI(unsigned long resp_len, 0x18, 0x100);
};

/*
 * RmiDevCommExitFlags
 * Fieldset contains flags provided by the RMM during a device transaction.
 * Width: 64 bits
 */
#define RMI_DEV_COMM_EXIT_FLAGS_CACHE_SHIFT		UL(0)
#define RMI_DEV_COMM_EXIT_FLAGS_CACHE_WIDTH		UL(1)
#define RMI_DEV_COMM_EXIT_FLAGS_SEND_SHIFT		UL(1)
#define RMI_DEV_COMM_EXIT_FLAGS_SEND_WIDTH		UL(1)
#define RMI_DEV_COMM_EXIT_FLAGS_WAIT_SHIFT		UL(2)
#define RMI_DEV_COMM_EXIT_FLAGS_WAIT_WIDTH		UL(1)
#define RMI_DEV_COMM_EXIT_FLAGS_MULTI_SHIFT		UL(3)
#define RMI_DEV_COMM_EXIT_FLAGS_MULTI_WIDTH		UL(1)

/*
 * RmiDevCommProtocol
 * Represents the protocol used for device communication.
 * Width: 8 bits
 */
#define RMI_DEV_COMM_PROTOCOL_SPDM		U(0)
#define RMI_DEV_COMM_PROTOCOL_SECURE_SPDM	U(1)

/*
 * RmiDevCommExit
 * This structure contains data passed from the RMM to the Host during device
 * communication.
 * Width: 256 (0x100) bytes.
 */
struct rmi_dev_comm_exit {
	/*
	 * RmiDevCommExitFlags: Flags indicating the actions the host is
	 * requested to perform
	 */
	SET_MEMBER_RMI(unsigned long flags, 0, 0x8);
	/*
	 * UInt64: If flags.cache is true, offset in the device response buffer
	 * to the start of data to be cached in bytes.
	 */
	SET_MEMBER_RMI(unsigned long cache_offset, 0x8, 0x10);
	/*
	 * UInt64: If flags.cache is true, amount of data to be cached in
	 * bytes.
	 */
	SET_MEMBER_RMI(unsigned long cache_len, 0x10, 0x18);
	/* RmiDevCommProtocol: If flags.send is true, type of request */
	SET_MEMBER_RMI(unsigned char protocol, 0x18, 0x20);
	/*
	 * UInt64: If flags.send is true, amount of valid data in request buffer
	 * in bytes
	 */
	SET_MEMBER_RMI(unsigned long req_len, 0x20, 0x28);
	/*
	 * UInt64: If flags.wait is true, amount of time to wait for device
	 * response in milliseconds
	 */
	SET_MEMBER_RMI(unsigned long timeout, 0x28, 0x100);
};

/*
 * RmiDevCommData
 * This structure contains data structure shared between Host and RMM for
 * device communication.
 * Width: 4096 (0x1000) bytes.
 */
#define RMI_DEV_COMM_ENTER_OFFSET		0x0
#define RMI_DEV_COMM_EXIT_OFFSET		0x800
#define RMI_DEV_COMM_DATA_SIZE			0x1000
struct rmi_dev_comm_data {
	/* RmiDevCommEnter: Entry information */
	SET_MEMBER_RMI(struct rmi_dev_comm_enter enter,
		       RMI_DEV_COMM_ENTER_OFFSET, RMI_DEV_COMM_EXIT_OFFSET);
	/* RmiDevCommExit: Exit information */
	SET_MEMBER_RMI(struct rmi_dev_comm_exit exit,
		       RMI_DEV_COMM_EXIT_OFFSET, RMI_DEV_COMM_DATA_SIZE);
};

/*
 * RmiAddressRange
 * This structure contains base and top value of an address range.
 * Width: 16 (0x10) bytes.
 */
struct rmi_address_range {
	/* Address: Base of the address range (inclusive) */
	SET_MEMBER_RMI(unsigned long base, 0, 0x8);
	/* Address: Top of the address range (exclusive) */
	SET_MEMBER_RMI(unsigned long top, 0x8, 0x10);
};

/*
 * Maximum number of aux granules paramenter passed in rmi_pdev_params during
 * PDEV createto PDEV create
 */
#define PDEV_PARAM_AUX_GRANULES_MAX		U(32)

/*
 * Maximum number of IO coherent RmiAddressRange parameter passed in
 * rmi_pdev_params during PDEV create
 */
#define PDEV_PARAM_IOCOH_ADDR_RANGE_MAX		U(16)

/*
 * Maximum number of fully coherent RmiAddressRange parameter passed in
 * rmi_pdev_params during PDEV create
 */
#define PDEV_PARAM_FCOH_ADDR_RANGE_MAX		U(4)

/*
 * RmiPdevParams
 * This structure contains parameters provided by Host during PDEV creation.
 * Width: 4096 (0x1000) bytes.
 */
struct rmi_pdev_params {
	/* RmiPdevFlags: Flags */
	SET_MEMBER_RMI(unsigned long flags, 0, 0x8);
	/* Bits64: Physical device identifier */
	SET_MEMBER_RMI(unsigned long pdev_id, 0x8, 0x10);
	/* Bits16: Segment ID */
	SET_MEMBER_RMI(unsigned short segment_id, 0x10, 0x18);
	/* Bits16: Root Port identifier */
	SET_MEMBER_RMI(unsigned short root_id, 0x18, 0x20);
	/* UInt64: Certificate identifier */
	SET_MEMBER_RMI(unsigned long cert_id, 0x20, 0x28);
	/* UInt64: Base requester ID range (inclusive) */
	SET_MEMBER_RMI(unsigned long rid_base, 0x28, 0x30);
	/* UInt64: Top of requester ID range (exclusive) */
	SET_MEMBER_RMI(unsigned long rid_top, 0x30, 0x38);
	/* RmiHashAlgorithm: Algorithm used to generate device digests */
	SET_MEMBER_RMI(unsigned char hash_algo, 0x38, 0x40);
	/* UInt64: Number of auxiliary granules */
	SET_MEMBER_RMI(unsigned long num_aux, 0x40, 0x48);
	/* UInt64: IDE stream identifier */
	SET_MEMBER_RMI(unsigned long ide_sid, 0x48, 0x50);
	/* UInt64: Number of IO-coherent address ranges */
	SET_MEMBER_RMI(unsigned long iocoh_num_addr_range, 0x50, 0x58);
	/* UInt64: Number of fully-coherent address ranges */
	SET_MEMBER_RMI(unsigned long fcoh_num_addr_range, 0x58, 0x100);

	/* Address: Addresses of auxiliary granules */
	SET_MEMBER_RMI(unsigned long aux[PDEV_PARAM_AUX_GRANULES_MAX], 0x100,
		       0x200);
	/* RmiAddressRange: IO-coherent address range */
	SET_MEMBER_RMI(struct rmi_address_range
		       iocoh_addr_range[PDEV_PARAM_IOCOH_ADDR_RANGE_MAX],
		       0x200, 0x300);
	/* RmiAddressRange: Fully coherent address range */
	SET_MEMBER_RMI(struct rmi_address_range
		       fcoh_addr_range[PDEV_PARAM_FCOH_ADDR_RANGE_MAX],
		       0x300, 0x1000);
};

/*
 * RmiVdevFlags
 * Fieldset contains flags provided by the Host during VDEV creation.
 * Width: 64 bits
 */
#define RMI_VDEV_FLAGS_RES0_SHIFT		UL(0)
#define RMI_VDEV_FLAGS_RES0_WIDTH		UL(63)

/*
 * RmiVdevState
 * Represents the state of the VDEV
 * Width: 8 bits
 */
#define RMI_VDEV_STATE_READY			U(0)
#define RMI_VDEV_STATE_COMMUNICATING		U(1)
#define RMI_VDEV_STATE_STOPPING			U(2)
#define RMI_VDEV_STATE_STOPPED			U(3)
#define RMI_VDEV_STATE_ERROR			U(4)

/* Maximum number of aux granules paramenter passed to VDEV create */
#define VDEV_PARAM_AUX_GRANULES_MAX		U(32)

/*
 * RmiVdevParams
 * The RmiVdevParams structure contains parameters provided by the Host during
 * VDEV creation.
 * Width: 4096 (0x1000) bytes.
 */
struct rmi_vdev_params {
	/* RmiVdevFlags: Flags */
	SET_MEMBER_RMI(unsigned long flags, 0, 0x8);
	/* Bits64: Virtual device identifier */
	SET_MEMBER_RMI(unsigned long vdev_id, 0x8, 0x10);
	/* Bits64: TDI identifier */
	SET_MEMBER_RMI(unsigned long tdi_id, 0x10, 0x18);
	/* UInt64: Number of auxiliary granules */
	SET_MEMBER_RMI(unsigned long num_aux, 0x18, 0x100);

	/* Address: Addresses of auxiliary granules */
	SET_MEMBER_RMI(unsigned long aux[VDEV_PARAM_AUX_GRANULES_MAX], 0x100,
		       0x1000);
};
#endif /* __ASSEMBLER__ */

#endif /* SMC_RMI_H */

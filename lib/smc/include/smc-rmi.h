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

#define MAKE_RMI_REVISION(_major, _minor)	(((_major) << UL(16)) | (_minor))
#define RMI_ABI_VERSION_GET_MAJOR(_version)	((_version) >> UL(16))
#define RMI_ABI_VERSION_GET_MINOR(_version)	((_version) & UL(0xFFFF))

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
 * On the primary RTT tree, an RTT walk terminated before reaching
 * the target RTT level, or reached an RTTE with an unexpected value.
 * index: RTT level at which the walk terminated
 *
 * If returned as output value for RMI_RTT_SET_S2AP then:
 * X1: `progress_addr` (IPA): The IPA where the RTT walk failed
 * X2: `rtt_tree` (IPA): The RTT tree where the RTT walk failed
 */
#define RMI_ERROR_RTT			U(4)

/* The command is not supported */
#define RMI_ERROR_NOT_SUPPORTED		U(5)

/* An attribute of a device does not match the expected value */
#define RMI_ERROR_DEVICE		U(6)

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
/* Maximum number of auxiliary planes supported */
#define MAX_AUX_PLANES			U(3)
#else /* CBMC */
#define MAX_REC_AUX_GRANULES		U(1)
#define MAX_AUX_PLANES			U(0)
#endif /* CBMC */

/* Total number of planes supported, including Plane 0 */
#define MAX_TOTAL_PLANES		(MAX_AUX_PLANES + 1U)

/* Whether Host has completed emulation for an Emulatable Data Abort */
#define REC_ENTRY_FLAG_EMUL_MMIO	(UL(1) << 0)

/* Whether to inject a Synchronous External Abort into Realm */
#define REC_ENTRY_FLAG_INJECT_SEA	(UL(1) << 1)

/* Whether to trap WFI/WFE execution by Realm */
#define REC_ENTRY_FLAG_TRAP_WFI		(UL(1) << 2)
#define REC_ENTRY_FLAG_TRAP_WFE		(UL(1) << 3)

/* Host response to RIPAS change request */
#define REC_ENTRY_FLAG_RIPAS_RESPONSE	(UL(1) << 4)

/* Host response to S2AP change request */
#define REC_ENTRY_FLAG_S2AP_RESPONSE	(UL(1) << 5)

/* Host response to device memory mapping validation request */
#define REC_ENTRY_FLAG_DEV_MEM_RESPONSE	(UL(1) << 6)

/* Whether to force control to return Plane 0 */
#define REC_ENTRY_FLAG_FORCE_P0		(UL(1) << 7)

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
#define RMI_EXIT_S2AP_CHANGE		U(7)
#define RMI_EXIT_VDEV_REQUEST		U(8)
#define RMI_EXIT_DEV_MEM_MAP		U(9)
#define RMI_EXIT_VDEV_P2P_BINDING	U(10)

/* RmiRttEntryState represents the state of an RTTE */
#define RMI_UNASSIGNED		UL(0)
#define RMI_ASSIGNED		UL(1)
#define RMI_TABLE		UL(2)
#define RMI_ASSIGNED_DEV	UL(3)
#define RMI_AUX_DESTROYED	UL(5)

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

#define RMI_FEATURE_REGISTER_0_MAX_NUM_AUX_PLANES_SHIFT UL(45)
#define RMI_FEATURE_REGISTER_0_MAX_NUM_AUX_PLANES_WIDTH UL(4)

#define RMI_FEATURE_REGISTER_0_RTT_S2AP_INDIRECT_SHIFT	UL(49)
#define RMI_FEATURE_REGISTER_0_RTT_S2AP_INDIRECT_WIDTH	UL(1)

#define RMI_FEATURE_REGISTER_1_INDEX			UL(1)
#define RMI_FEATURE_REGISTER_1_MAX_MECID_SHIFT		UL(0)
#define RMI_FEATURE_REGISTER_1_MAX_MECID_WIDTH		UL(64)

/* The RmiRipas enumeration represents realm IPA state */

/* Address where no Realm resources are mapped */
#define RMI_EMPTY	UL(0)

/* Address where private code or data owned by the Realm is mapped */
#define RMI_RAM		UL(1)

/* Address which is inaccessible to the Realm due to an action taken by the Host */
#define RMI_DESTROYED	UL(2)

/* Address where memory of an assigned Realm device is mapped */
#define RMI_DEV		UL(3)

/* RmiPmuOverflowStatus enumeration representing PMU overflow status */
#define RMI_PMU_OVERFLOW_NOT_ACTIVE	U(0)
#define RMI_PMU_OVERFLOW_ACTIVE		U(1)

/* Possible values for RmiRttPlaneFeature */
#define RMI_RTT_PLANE_AUX		UL(0)
#define RMI_RTT_PLANE_AUX_SINGLE	UL(1)
#define RMI_RTT_PLANE_SINGLE		UL(2)

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
 *
 * ret1 == Top of the non-live address region. Only valid
 *         if ret0 == RMI_SUCCESS or ret0 == (RMI_ERROR_RTT, x)
 */
#define SMC_RMI_RTT_UNMAP_UNPROTECTED		SMC64_RMI_FID(U(0x12))

/*
 * FID: 0xC4000163
 *
 * arg0 == PA of the RD for the target Realm
 * arg1 == PA of the target REC
 * arg2 == PA of the PDEV
 * arg3 == PA of the VDEV
 * arg4 == Base of target IPA region
 * arg5 == Top of target IPA region
 *
 * ret1 == Top IPA of range whose RIPAS was modified
 */
#define SMC_RMI_VDEV_VALIDATE_MAPPING		SMC64_RMI_FID(U(0x13))

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
 * FID: 0xC400016A
 */
#define SMC_RMI_VSMMU_CREATE			SMC64_RMI_FID(U(0x1A))

/*
 * FID: 0xC400016B
 */
#define SMC_RMI_VSMMU_DESTROY			SMC64_RMI_FID(U(0x1B))

/*
 * FID: 0xC400016C
 */
#define SMC_RMI_VSMMU_MAP			SMC64_RMI_FID(U(0x1C))

/*
 * FID: 0xC400016D
 */
#define SMC_RMI_VSMMU_UNMAP			SMC64_RMI_FID(U(0x1D))

/*
 * FID: 0xC400016E
 */
#define SMC_RMI_PSMMU_MSI_CONFIG		SMC64_RMI_FID(U(0x1E))

/*
 * FID: 0xC400016F
 */
#define SMC_RMI_PSMMU_IRQ_NOTIFY		SMC64_RMI_FID(U(0x1F))

/*
 * FID: 0xC4000170 and 0xC4000171 are not used.
 */

/*
 * FID: 0xC4000172
 *
 * arg0 == PA of the RD for the target Realm
 * arg1 == PA of the VDEV
 * arg2 == IPA at which the memory will be mapped in the target Realm
 * arg3 == RTT level
 * arg4 == PA of the target device memory
 */
#define SMC_RMI_VDEV_MAP			SMC64_RMI_FID(U(0x22))

/*
 * FID: 0xC4000173
 *
 * arg0 == PA of the RD which owns the target device memory
 * arg1 == IPA at which the memory is mapped in the target Realm
 * arg2 == RTT level
 *
 * ret1 == PA of the device memory which was unmapped
 * ret2 == Top IPA of non-live RTT entries, from entry at which the RTT walk
 *         terminated
 */
#define SMC_RMI_VDEV_UNMAP			SMC64_RMI_FID(U(0x23))

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
 *
 * arg0 == PA of the PDEV
 * arg1 == Select coherent or non-coherent IDE stream
 */
#define SMC_RMI_PDEV_IDE_KEY_REFRESH		SMC64_RMI_FID(U(0x2A))

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
 *
 * arg0 == RD address
 * arg1 == RTT address
 * arg2 == map address
 * arg3 == level
 * arg4 == RTT Tree index
 */
#define SMC_RMI_RTT_AUX_CREATE			SMC64_RMI_FID(U(0x2D))

/*
 * FID: 0xC400017D
 *
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 * arg3 == RTT Tree index
 *
 * ret1 == Address (PA) of the RTT, if ret0 == RMI_SUCCESS
 *         Otherwise, undefined.
 * ret2 == Top of the non-live address region. Only valid
 *         if ret0 == RMI_SUCCESS or ret0 == (RMI_ERROR_RTT, x)
 */
#define SMC_RMI_RTT_AUX_DESTROY			SMC64_RMI_FID(U(0x2E))

/*
 * FID: 0xC400017F
 *
 * arg0 == RD address
 * arg1 == map address
 * arg2 == level
 * arg3 == RTT Tree index
 *
 * ret1 == Address(PA) of the RTT folded, if ret0 == RMI_SUCCESS
 */
#define SMC_RMI_RTT_AUX_FOLD			SMC64_RMI_FID(U(0x2F))

/*
 * FID: 0xC4000180
 *
 * arg0 == RD address
 * arg1 == map address
 * arg2 == RTT Tree index
 *
 * ret1 == index of the RTT Tree that caused a failure
 * ret2 == level of RTTE reached by a walk of the primary RTT tree
 * ret3 == state of RTTE which caused RMI_ERROR_RTT
 * ret4 == ripas of the RTTE which caused RMI_ERROR_RTT
 * if ret0 == RMI_SUCCESS, otherwise, undefined.
 */
#define SMC_RMI_RTT_AUX_MAP_PROTECTED		SMC64_RMI_FID(U(0x30))

/*
 * FID: 0xC4000181
 *
 * arg0 == RD address
 * arg1 == map address
 * arg2 == RTT Tree index
 *
 * ret1 == index of the RTT Tree that caused a failure
 * ret2 == level of RTTE reached by a walk of the primary RTT tree
 * ret3 == state of RTTE which caused RMI_ERROR_RTT
 * if ret0 == RMI_SUCCESS, otherwise, undefined.
 */
#define SMC_RMI_RTT_AUX_MAP_UNPROTECTED		SMC64_RMI_FID(U(0x31))

/*
 * FID: 0xC4000182 is not used.
 */

/*
 * FID: 0xC4000183
 * arg0 == RD address
 * arg1 == unmap address
 * arg2 == RTT Tree index
 *
 * ret1 == Top IPA of non-live RTT entries from entry at which the RTT walk terminated
 * if ret0 == RMI_SUCCESS, otherwise, undefined.
 */
#define SMC_RMI_RTT_AUX_UNMAP_PROTECTED		SMC64_RMI_FID(U(0x33))

/*
 * FID: 0xC4000184
 *
 * arg0 == RD address
 * arg1 == unmap address
 * arg2 == RTT Tree index
 *
 * ret1 == Top IPA of non-live RTT entries from entry at which the RTT walk terminated
 * ret2 == level of RTTE reached by a walk of the RTT
 * if ret0 == RMI_SUCCESS, otherwise, undefined.
 */
#define SMC_RMI_RTT_AUX_UNMAP_UNPROTECTED	SMC64_RMI_FID(U(0x34))

/*
 * FID: 0xC4000185
 */
#define SMC_RMI_VDEV_ABORT			SMC64_RMI_FID(U(0x35))

/*
 * FID: 0xC4000186
 *
 * arg0 == PA of the RD
 * arg1 == PA of the PDEV
 * arg2 == PA of the VDEV
 * arg3 == PA of the communication data structure
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
 *
 * arg0 == PA of the RD
 * arg1 == PA of the PDEV
 * arg2 == PA of the VDEV
 */
#define SMC_RMI_VDEV_UNLOCK			SMC64_RMI_FID(U(0x3A))

/*
 * FID: 0xC400018B
 *
 * arg0 == RD address
 * arg1 == REC address
 * arg2 == Start address
 * arg3 == End address
 *
 * ret1 == Top of the address range where the S2AP was updated,
 *	   if ret0 == RMI_SUCCESS
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

/*
 * FID: 0xC400018F is not used.
 */

/*
 * Revised 64-bit Arm CCA function ID range reservation is
 * 0xC400_0150 - 0xC400_02CF
 *
 * Within this range RMI FIDs allocation is split in two ranges:
 *
 * 0xC4000150 - 0xC400018F - RMI FID range1
 * 0xC4000190 - 0xC40001BF - RSI FID range
 * 0xC40001D0 - 0xC40001D3 - RMI FID range2
 */

/*
 * FID: 0xC40001D0
 *
 * arg0 == PA of the RD
 * arg1 == PA of the PDEV
 * arg2 == PA of the VDEV
 */
#define SMC_RMI_VDEV_GET_INTERFACE_REPORT	SMC64_RMI_FID(U(0x80))

/*
 * FID: 0xC40001D1
 *
 * arg0 == PA of the RD
 * arg1 == PA of the PDEV
 * arg2 == PA of the VDEV
 * arg3 == PA of VDEV parameters
 */
#define SMC_RMI_VDEV_GET_MEASUREMENTS		SMC64_RMI_FID(U(0x81))

/*
 * FID: 0xC40001D2
 *
 * arg0 == PA of the RD
 * arg1 == PA of the PDEV
 * arg2 == PA of the VDEV
 */
#define SMC_RMI_VDEV_LOCK			SMC64_RMI_FID(U(0x82))

/*
 * FID: 0xC40001D3
 *
 * arg0 == PA of the RD
 * arg1 == PA of the PDEV
 * arg2 == PA of the VDEV
 */
#define SMC_RMI_VDEV_START			SMC64_RMI_FID(U(0x83))

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

/* RmiRealmFlags0 format */
#define RMI_REALM_FLAGS0_LPA2_SHIFT	UL(0)
#define RMI_REALM_FLAGS0_LPA2_WIDTH	UL(1)

#define RMI_REALM_FLAGS0_SVE_SHIFT	UL(1)
#define RMI_REALM_FLAGS0_SVE_WIDTH	UL(1)

#define RMI_REALM_FLAGS0_PMU_SHIFT	UL(2)
#define RMI_REALM_FLAGS0_PMU_WIDTH	UL(1)

#define RMI_REALM_FLAGS0_DA_SHIFT	UL(3)
#define RMI_REALM_FLAGS0_DA_WIDTH	UL(1)

/* RmiRealmFlags1 format */
#define RMI_REALM_FLAGS1_RTT_TREE_PP_SHIFT	UL(0)
#define RMI_REALM_FLAGS1_RTT_TREE_PP_WIDTH	UL(1)

#define RMI_REALM_FLAGS1_S2AP_ENC_SHIFT		UL(1)
#define RMI_REALM_FLAGS1_S2AP_ENC_WIDTH		UL(1)

/* Possible values for RmiRttS2APEncoding flag */
#define RMI_S2AP_DIRECT				UL(0)
#define RMI_S2AP_INDIRECT			UL(1)

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
	SET_MEMBER_RMI(unsigned long flags0, 0, 0x8);			/* Offset 0 */
	/* Requested IPA width */
	SET_MEMBER_RMI(unsigned int s2sz, 0x8, 0x10);			/* 0x8 */
	/* Requested SVE vector length */
	SET_MEMBER_RMI(unsigned int sve_vl, 0x10, 0x18);		/* 0x10 */
	/* Requested number of breakpoints */
	SET_MEMBER_RMI(unsigned int num_bps, 0x18, 0x20);		/* 0x18 */
	/* Requested number of watchpoints */
	SET_MEMBER_RMI(unsigned int num_wps, 0x20, 0x28);		/* 0x20 */
	/* Requested number of PMU counters */
	SET_MEMBER_RMI(unsigned int pmu_num_ctrs, 0x28, 0x30);		/* 0x28 */
	/* Measurement algorithm */
	SET_MEMBER_RMI(unsigned char algorithm, 0x30, 0x38);		/* 0x30 */
	/* Number of auxiliary Planes */
	SET_MEMBER_RMI(unsigned int num_aux_planes, 0x38, 0x400);
	/* Realm Personalization Value */
	SET_MEMBER_RMI(unsigned char rpv[RPV_SIZE], 0x400, 0x440);	/* 0x400 */
	/*
	 * If ATS is enabled, determines the stage 2 translation used by devices
	 * assigned to the Realm.
	 */
	SET_MEMBER_RMI(unsigned long ats_plane, 0x440, 0x800);		/* 0x440 */

	SET_MEMBER_RMI(struct {
			/* Virtual Machine Identifier */
			unsigned short vmid;				/* 0x800 */
			/* Realm Translation Table base */
			unsigned long rtt_base;				/* 0x808 */
			/* RTT starting level */
			long rtt_level_start;				/* 0x810 */
			/* Number of starting level RTTs */
			unsigned int rtt_num_start;			/* 0x818 */
		   }, 0x800, 0x820);
	/* RmiRealmFlags1 */
	SET_MEMBER_RMI(unsigned long flags1, 0x820, 0x828);		/* 0x820 */
	/* MECID */
	SET_MEMBER_RMI(long mecid, 0x828, 0xF00);			/* 0x828 */
	/* Auxiliary Virtual Machine Identifiers */
	SET_MEMBER_RMI(unsigned short aux_vmid[3], 0xF00, 0xF80);	/* 0xF00 */
	/* Base address of auxiliary RTTs */
	SET_MEMBER_RMI(unsigned long aux_rtt_base[3], 0xF80, 0x1000);	/* 0xF80 */
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
	SET_MEMBER_RMI(unsigned long exit_reason, 0, 0x100);/* Offset 0 */
	SET_MEMBER_RMI(struct {
			/* Exception Syndrome Register */
			unsigned long esr;		/* 0x100 */
			/* Fault Address Register */
			unsigned long far;		/* 0x108 */
			/* Hypervisor IPA Fault Address register */
			unsigned long hpfar;		/* 0x110 */
			/* Index of RTT tree active at time of exit */
			unsigned long rtt_tree;		/* 0x118 */
			/* Level of requested RTT */
			long rtt_level;			/* 0x120 */
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
		   }, 0x500, 0x520);
	SET_MEMBER_RMI(struct {
			/* Base addr of target region for pending S2AP change */
			unsigned long s2ap_base; /* 0x520 */
			/* Top addr of target region for pending S2AP change */
			unsigned long s2ap_top; /* 0x528 */
			/* Virtual device ID 1 */
			unsigned long vdev_id_1; /* 0x530 */
			/* Virtual device ID 2 */
			unsigned long vdev_id_2; /* 0x538 */
			/* Base IPA of target region for VDEV mapping validation */
			unsigned long dev_mem_base; /* 0x540 */
			/* Top IPA of target region for VDEV mapping validation */
			unsigned long dev_mem_top; /* 0x548 */
			/* Base PA of device memory region */
			unsigned long dev_mem_pa; /* 0x550 */
		   }, 0x520, 0x600);

	/* Host call immediate value */
	SET_MEMBER_RMI(unsigned int imm, 0x600, 0x608);
	/* UInt64: Plane Index */
	SET_MEMBER_RMI(unsigned long plane, 0x608, 0x700);
	/* PMU overflow status */
	SET_MEMBER_RMI(unsigned long pmu_ovf_status, 0x700, 0x800);
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
 * RmiPdevSpdm
 * Represents whether communication with the device uses SPDM.
 * Width: 1 bit
 */
#define RMI_PDEV_SPDM_FALSE			U(0)
#define RMI_PDEV_SPDM_TRUE			U(1)

/*
 * RmiPdevIde
 * Represents whether the link to the device is protected using IDE.
 * Width: 1 bit
 */
#define RMI_PDEV_IDE_FALSE			U(0)
#define RMI_PDEV_IDE_TRUE			U(1)

/*
 * RmiPdevCoherent
 * Represents the device access is non-coherent or coherent
 * Width: 1 bit
 */
#define RMI_PDEV_COHERENT_FALSE			U(0)
#define RMI_PDEV_COHERENT_TRUE			U(1)

/*
 * RmiPdevTrust
 * Represents the device trust model.
 * Width: 1 bit
 */
#define RMI_TRUST_SEL				U(0)
#define RMI_TRUST_COMP				U(1)

/*
 * RmiPdevCategory
 * Represents PDEV category.
 * Width: 2 bits
 */
#define RMI_PDEV_SMEM				U(0)
#define RMI_PDEV_CMEM_CXL			U(1)

/*
 * RmiPdevFlags
 * Fieldset contains flags provided by the Host during PDEV creation
 * Width: 64 bits
 */
/* RmiPdevSpdm: Bit 0 */
#define RMI_PDEV_FLAGS_SPDM_SHIFT		UL(0)
#define RMI_PDEV_FLAGS_SPDM_WIDTH		UL(1)
/* RmiPdevIde: Bit 1 */
#define RMI_PDEV_FLAGS_NCOH_IDE_SHIFT		UL(1)
#define RMI_PDEV_FLAGS_NCOH_IDE_WIDTH		UL(1)
/* RmiFeature: Bit 2 */
#define RMI_PDEV_FLAGS_NCOH_ADDR_SHIFT		UL(2)
#define RMI_PDEV_FLAGS_NCOH_ADDR_WIDTH		UL(1)
/* RmiPdevIde: Bit 3 */
#define RMI_PDEV_FLAGS_COH_IDE_SHIFT		UL(3)
#define RMI_PDEV_FLAGS_COH_IDE_WIDTH		UL(1)
/* RmiFeature: Bit 4 */
#define RMI_PDEV_FLAGS_COH_ADDR_SHIFT		UL(4)
#define RMI_PDEV_FLAGS_COH_ADDR_WIDTH		UL(1)
/* RmiFeature: Bit 5 */
#define RMI_PDEV_FLAGS_P2P_SHIFT		UL(5)
#define RMI_PDEV_FLAGS_P2P_WIDTH		UL(1)
/* RmiPdevTrust: Bit 6 */
#define RMI_PDEV_FLAGS_TRUST_SHIFT		UL(6)
#define RMI_PDEV_FLAGS_TRUST_WIDTH		UL(1)
/* RmiPdevCategory: Bit 8-7 */
#define RMI_PDEV_FLAGS_CATEGORY_SHIFT		UL(7)
#define RMI_PDEV_FLAGS_CATEGORY_WIDTH		UL(2)

/*
 * RmiPdevEvent
 * Represents physical device event.
 * Width: 8 bits
 */
#define RMI_PDEV_EVENT_IDE_KEY_REFRESH		U(0)

/*
 * RmmPdevState
 * Represents the state of a PDEV
 * Width: 8 bits
 */
#define RMI_PDEV_STATE_NEW			U(0)
#define RMI_PDEV_STATE_NEEDS_KEY		U(1)
#define RMI_PDEV_STATE_HAS_KEY			U(2)
#define RMI_PDEV_STATE_READY			U(3)
#define RMI_PDEV_STATE_IDE_RESETTING		U(4)
#define RMI_PDEV_STATE_COMMUNICATING		U(5)
#define RMI_PDEV_STATE_STOPPING			U(6)
#define RMI_PDEV_STATE_STOPPED			U(7)
#define RMI_PDEV_STATE_ERROR			U(8)

/*
 * RmiSignatureAlgorithm
 * Represents signature algorithm used in PDEV set key RMI call.
 * Width: 8 bits
 */
#define RMI_SIGNATURE_ALGORITHM_RSASSA_3072	U(0)
#define RMI_SIGNATURE_ALGORITHM_ECDSA_P256	U(1)
#define RMI_SIGNATURE_ALGORITHM_ECDSA_P384	U(2)

/*
 * RmiDevCommEnterStatus (Name in Spec RmiDevCommStatus)
 * Represents status passed from the Host to the RMM during device communication.
 * Width: 8 bits
 */
#define RMI_DEV_COMM_ENTER_STATUS_NONE		U(0)
#define RMI_DEV_COMM_ENTER_STATUS_RESPONSE	U(1)
#define RMI_DEV_COMM_ENTER_STATUS_ERROR		U(2)

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
#define RMI_DEV_COMM_EXIT_FLAGS_REQ_CACHE_BIT		(UL(1) << 0U)
#define RMI_DEV_COMM_EXIT_FLAGS_RSP_CACHE_BIT		(UL(1) << 1U)
#define RMI_DEV_COMM_EXIT_FLAGS_REQ_SEND_BIT		(UL(1) << 2U)
#define RMI_DEV_COMM_EXIT_FLAGS_RSP_WAIT_BIT		(UL(1) << 3U)
#define RMI_DEV_COMM_EXIT_FLAGS_RSP_RESET_BIT		(UL(1) << 4U)
#define RMI_DEV_COMM_EXIT_FLAGS_MULTI_BIT		(UL(1) << 5U)

/*
 * RmiDevCommObject
 * This represents identifier of a device communication object which the Host is
 * requested to cache.
 * Width: 8 bits
 */
#define RMI_DEV_COMM_OBJECT_VCA			U(0)
#define RMI_DEV_COMM_OBJECT_CERTIFICATE		U(1)
#define RMI_DEV_COMM_OBJECT_MEASUREMENTS	U(2)
#define RMI_DEV_COMM_OBJECT_INTERFACE_REPORT	U(3)

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
	 * UInt64: If flags.cache_req is true, offset in the device request
	 * buffer to the start of data to be cached, in bytes
	 */
	SET_MEMBER_RMI(unsigned long cache_req_offset, 0x8, 0x10);
	/*
	 * UInt64: If flags.cache_req is true, amount of device request data to
	 * be cached, in bytes
	 */
	SET_MEMBER_RMI(unsigned long cache_req_len, 0x10, 0x18);
	/*
	 * UInt64: If flags.cache_rsp is true, offset in the device response
	 * buffer to the start of data to be cached, in bytes
	 */
	SET_MEMBER_RMI(unsigned long cache_rsp_offset, 0x18, 0x20);
	/*
	 * UInt64: If flags.cache_rsp is true, amount of device response data to
	 * be cached, in bytes.
	 */
	SET_MEMBER_RMI(unsigned long cache_rsp_len, 0x20, 0x28);
	/*
	 * RmiDevCommObject: If flags.cache_req is true and / or flags.cache_rsp
	 * is true, identifier for the object to be cachedIf flags.cache_rsp is
	 * true, amount of device response data to be cached, in bytes.
	 */
	SET_MEMBER_RMI(unsigned char cache_obj_id, 0x28, 0x30);
	/* RmiDevCommProtocol: If flags.send is true, type of request */
	SET_MEMBER_RMI(unsigned char protocol, 0x30, 0x38);
	/*
	 * UInt64: If flags.req_send is true, amount of time to wait before
	 * sending the request, in microseconds.
	 */
	SET_MEMBER_RMI(unsigned char req_delay, 0x38, 0x40);
	/*
	 * UInt64: If flags.send is true, amount of valid data in request buffer
	 * in bytes
	 */
	SET_MEMBER_RMI(unsigned long req_len, 0x40, 0x48);
	/*
	 * UInt64: If flags.wait is true, amount of time to wait for device
	 * response in milliseconds
	 */
	SET_MEMBER_RMI(unsigned long timeout, 0x48, 0x100);
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

/* cppcheck-suppress misra-c2012-2.4 */
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

#ifdef CBMC
#define PDEV_PARAM_NCOH_ADDR_RANGE_MAX		U(1)
#else /* CBMC */
/*
 * Maximum number of device non-coherent RmiAddressRange parameter passed in
 * rmi_pdev_params during PDEV create
 */
#define PDEV_PARAM_NCOH_ADDR_RANGE_MAX		U(16)
#endif /* CBMC */

/*
 * Maximum number of device coherent RmiAddressRange parameter passed in
 * rmi_pdev_params during PDEV create
 */
#define PDEV_PARAM_COH_ADDR_RANGE_MAX		U(4)

/*
 * RmiPdevParams
 * This structure contains parameters provided by Host during PDEV creation.
 * Width: 4096 (0x1000) bytes.
 */
/* cppcheck-suppress misra-c2012-2.4 */
struct rmi_pdev_params {
	/* RmiPdevFlags: Flags */
	SET_MEMBER_RMI(unsigned long flags, 0, 0x8);
	/* Bits64: Physical device identifier */
	SET_MEMBER_RMI(unsigned long pdev_id, 0x8, 0x10);
	/* Bits8: Segment ID */
	SET_MEMBER_RMI(unsigned char segment_id, 0x10, 0x18);
	/* Address: ECAM base address of the PCIe configuration space */
	SET_MEMBER_RMI(unsigned long ecam_addr, 0x18, 0x20);
	/* Bits16: Root Port identifier */
	SET_MEMBER_RMI(unsigned short root_id, 0x20, 0x28);
	/* UInt64: Certificate identifier */
	SET_MEMBER_RMI(unsigned long cert_id, 0x28, 0x30);
	/* UInt16: Base requester ID range (inclusive) */
	SET_MEMBER_RMI(unsigned short rid_base, 0x30, 0x38);
	/* UInt16: Top of requester ID range (exclusive) */
	SET_MEMBER_RMI(unsigned short rid_top, 0x38, 0x40);
	/* RmiHashAlgorithm: Algorithm used to generate device digests */
	SET_MEMBER_RMI(unsigned char hash_algo, 0x40, 0x48);
	/* UInt64: Number of auxiliary granules */
	SET_MEMBER_RMI(unsigned long num_aux, 0x48, 0x50);
	/* UInt64: IDE stream identifier */
	SET_MEMBER_RMI(unsigned long ide_sid, 0x50, 0x58);
	/* UInt64: Number of device non-coherent address ranges */
	SET_MEMBER_RMI(unsigned long ncoh_num_addr_range, 0x58, 0x60);
	/* UInt64: Number of device coherent address ranges */
	SET_MEMBER_RMI(unsigned long coh_num_addr_range, 0x60, 0x100);
	/* Address: Addresses of auxiliary granules */
	SET_MEMBER_RMI(unsigned long aux[PDEV_PARAM_AUX_GRANULES_MAX], 0x100,
		       0x200);
	/* RmiAddressRange: Device non-coherent address range */
	SET_MEMBER_RMI(struct rmi_address_range
		       ncoh_addr_range[PDEV_PARAM_NCOH_ADDR_RANGE_MAX],
		       0x200, 0x300);
	/* RmiAddressRange: Device coherent address range */
	SET_MEMBER_RMI(struct rmi_address_range
		       coh_addr_range[PDEV_PARAM_COH_ADDR_RANGE_MAX],
		       0x300, 0x1000);
};

/* Max length of public key data passed in rmi_public_key_params */
#define PUBKEY_PARAM_KEY_LEN_MAX	U(1024)

/* Max length of public key metadata passed in rmi_public_key_params */
#define PUBKEY_PARAM_METADATA_LEN_MAX	U(1024)

/*
 * RmiPublicKeyParams
 * This structure contains public key parameters.
 * Width: 4096 (0x1000) bytes.
 */
/* cppcheck-suppress misra-c2012-2.4 */
struct rmi_public_key_params {
	/* Bits8: Key data */
	SET_MEMBER_RMI(unsigned char key[PUBKEY_PARAM_KEY_LEN_MAX], 0x0, 0x400);
	/* Bits8: Key metadata */
	SET_MEMBER_RMI(unsigned char metadata[PUBKEY_PARAM_METADATA_LEN_MAX],
		       0x400, 0x800);
	/* UInt64: Length of key data in bytes */
	SET_MEMBER_RMI(unsigned long key_len, 0x800, 0x808);
	/* UInt64: Length of metadata in bytes */
	SET_MEMBER_RMI(unsigned long metadata_len, 0x808, 0x810);
	/* RmiSignatureAlgorithm: Signature algorithm */
	SET_MEMBER_RMI(unsigned char algo, 0x810, 0x1000);
};

/*
 * RmiVdevFlags
 * Fieldset contains flags provided by the Host during VDEV creation.
 * Width: 64 bits
 */
#define RMI_VDEV_FLAGS_RES0_SHIFT		UL(0)
#define RMI_VDEV_FLAGS_RES0_WIDTH		UL(63)

/*
 * RmmVdevState
 * Represents the state of the VDEV
 * Width: 8 bits
 */
#define RMI_VDEV_STATE_NEW			U(0)
#define RMI_VDEV_STATE_UNLOCKED			U(1)
#define RMI_VDEV_STATE_LOCKED			U(2)
#define RMI_VDEV_STATE_STARTED			U(3)
#define RMI_VDEV_STATE_ERROR			U(4)
#define RMI_VDEV_STATE_KEY_REFRESH		U(5)
#define RMI_VDEV_STATE_KEY_PURGE		U(6)

/* Maximum number of aux granules paramenter passed to VDEV create */
#define VDEV_PARAM_AUX_GRANULES_MAX		U(32)

/*
 * RmiVdevParams
 * The RmiVdevParams structure contains parameters provided by the Host during
 * VDEV creation.
 * Width: 4096 (0x1000) bytes.
 */
/* cppcheck-suppress misra-c2012-2.4 */
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

/*
 * RmiVdevMeasureFlags
 * Fieldset contains flags which describe properties of device measurements.
 * Width: 64 bits
 */
/* RmiVdevMeasureRaw */
#define RMI_VDEV_MEASURE_FLAGS_RAW_SHIFT	U(0)
#define RMI_VDEV_MEASURE_FLAGS_RAW_WIDTH	U(1)

#define VDEV_MEAS_PARAM_NONCE_LEN		U(32)

/*
 * RmiVdevMeasureParams
 * This structure contains device measurement parameters.
 * Width: 4096 (0x1000) bytes.
 */
/* cppcheck-suppress misra-c2012-2.4 */
struct rmi_vdev_measure_params {
	/* RmiVdevMeasureFlags: Properties of device measurements */
	SET_MEMBER_RMI(unsigned long flags, 0, 0x100);
	/* Bits256: Nonce value used in measurement requests */
	SET_MEMBER_RMI(unsigned char nonce[VDEV_MEAS_PARAM_NONCE_LEN], 0x100, 0x1000);
};

/*
 * RmmVdevDmaState
 * Represents the state of DMA for a VDEV.
 * Width: 8 bits
 */
#define RMI_VDEV_DMA_DISABLED		U(0)
#define RMI_VDEV_DMA_ENABLED		U(1)

/* Returns the higher supported RMI ABI revision */
unsigned long rmi_get_highest_supported_version(void);
#endif /* __ASSEMBLER__ */

#endif /* SMC_RMI_H */

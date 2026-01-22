/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SMC_RSI_H
#define SMC_RSI_H

#include <smc.h>
#include <utils_def.h>

/*
 * This file describes the Realm Services Interface (RSI) Application Binary
 * Interface (ABI) for SMC calls made from within the Realm to the RMM and
 * serviced by the RMM.
 */

#define MAKE_RSI_REVISION(_major, _minor)	(((_major) << UL(16)) | (_minor))
#define RSI_ABI_VERSION_GET_MAJOR(_version)	((_version) >> UL(16))
#define RSI_ABI_VERSION_GET_MINOR(_version)	((_version) & UL(0xFFFF))

#define IS_SMC64_RSI_FID(_fid)		IS_SMC64_STD_FAST_IN_RANGE(RSI, _fid)

#define SMC64_RSI_FID(_offset)		SMC64_STD_FID(RSI, _offset)

/*
 * RsiCommandReturnCode enumeration
 * representing a return code from an RSI command.
 */
/* Command completed successfully */
#define RSI_SUCCESS		UL(0)

/* The value of a command input value caused the command to fail */
#define RSI_ERROR_INPUT		UL(1)

/*
 * The state of the current Realm or current REC
 * does not match the state expected by the command
 */
#define RSI_ERROR_STATE		UL(2)

/* The operation requested by the command is not complete */
#define RSI_INCOMPLETE		UL(3)

/* The operation requested by the command failed for an unknown reason */
#define RSI_ERROR_UNKNOWN	UL(4)

/*
 * The state of a Realm device does not match the state expected by the command.
 */
#define RSI_ERROR_DEVICE	UL(5)

#define RSI_ERROR_COUNT_MAX	UL(6)

/* RsiHashAlgorithm */
#define RSI_HASH_SHA_256	0U
#define RSI_HASH_SHA_512	1U

/*
 * RsiRipasChangeDestroyed:
 * RIPAS change from DESTROYED should not be permitted
 */
#define RSI_NO_CHANGE_DESTROYED	U(0)

/* A RIPAS change from DESTROYED should be permitted */
#define RSI_CHANGE_DESTROYED	U(1)

/*
 * RsiResponse enumeration represents whether Host accepted
 * or rejected a Realm request
 */
#define RSI_ACCEPT		U(0)
#define RSI_REJECT		U(1)

/*
 * FID: 0xC4000190
 *
 * Returns RSI version.
 * arg1: Requested interface version
 * ret0: Status / error
 * ret1: Lower implemented interface revision
 * ret2: Higher implemented interface revision
 */
#define SMC_RSI_VERSION			SMC64_RSI_FID(U(0x0))

/*
 * FID: 0xC4000191
 *
 * Returns RSI Feature register requested by index.
 * arg1: Feature register index
 * ret0: Status / error
 * ret1: Feature register value
 */
#define SMC_RSI_FEATURES		SMC64_RSI_FID(U(0x1))

/*
 * FID: 0xC4000192
 *
 * Returns a measurement.
 * arg1: Measurement index (0..4), measurement (RIM or REM) to read
 * ret0: Status / error
 * ret1: Measurement value, bytes:  0 -  7
 * ret2: Measurement value, bytes:  8 - 15
 * ret3: Measurement value, bytes: 16 - 23
 * ret4: Measurement value, bytes: 24 - 31
 * ret5: Measurement value, bytes: 32 - 39
 * ret6: Measurement value, bytes: 40 - 47
 * ret7: Measurement value, bytes: 48 - 55
 * ret8: Measurement value, bytes: 56 - 63
 */
#define SMC_RSI_MEASUREMENT_READ	SMC64_RSI_FID(U(0x2))

/*
 * FID: 0xC4000193
 *
 * Extends a REM.
 * arg1:  Measurement index (1..4), measurement (REM) to extend
 * arg2:  Measurement size in bytes
 * arg3:  Challenge value, bytes:  0 -  7
 * arg4:  Challenge value, bytes:  8 - 15
 * arg5:  Challenge value, bytes: 16 - 23
 * arg6:  Challenge value, bytes: 24 - 31
 * arg7:  Challenge value, bytes: 32 - 39
 * arg8:  Challenge value, bytes: 40 - 47
 * arg9:  Challenge value, bytes: 48 - 55
 * arg10: Challenge value, bytes: 56 - 63
 * ret0:  Status / error
 */
#define SMC_RSI_MEASUREMENT_EXTEND	SMC64_RSI_FID(U(0x3))

/*
 * FID: 0xC4000194
 *
 * Initialize the operation to retrieve an attestation token.
 * arg1: Challenge value, bytes:  0 -  7
 * arg2: Challenge value, bytes:  8 - 15
 * arg3: Challenge value, bytes: 16 - 23
 * arg4: Challenge value, bytes: 24 - 31
 * arg5: Challenge value, bytes: 32 - 39
 * arg6: Challenge value, bytes: 40 - 47
 * arg7: Challenge value, bytes: 48 - 55
 * arg8: Challenge value, bytes: 56 - 63
 * ret0: Status / error
 * ret1: Upper bound on attestation token size in bytes
 */
#define SMC_RSI_ATTEST_TOKEN_INIT	SMC64_RSI_FID(U(0x4))

/*
 * FID: 0xC4000195
 *
 * Continue the operation to retrieve an attestation token.
 * arg1: IPA of the Granule to which the token will be written
 * arg2: Offset within Granule to start of buffer in bytes
 * arg3: Size of buffer in bytes
 * ret0: Status / error
 * ret1: Number of bytes written to buffer
 */
#define SMC_RSI_ATTEST_TOKEN_CONTINUE	SMC64_RSI_FID(U(0x5))

/*
 * FID: 0xC4000196
 *
 * Read configuration for the current Realm.
 * arg1 == IPA of the Granule to which the configuration data will be written
 * ret0 == Status / error
 */
#define SMC_RSI_REALM_CONFIG		SMC64_RSI_FID(U(0x6))

/*
 * FID: 0xC4000197
 *
 * arg1 == Base IPA address of target region
 * arg2 == Top address of target region
 * arg3 == RIPAS value
 * arg4 == flags
 * ret0 == Status / error
 * ret1 == Base of IPA region which was not modified by the command
 * ret2 == RSI response
 */
#define SMC_RSI_IPA_STATE_SET		SMC64_RSI_FID(U(0x7))

/*
 * FID: 0xC4000198
 *
 * arg1 == Base of target IPA region
 * arg2 == End of target IPA region
 * ret0 == Status / error
 * ret1 == Top of IPA region which has the reported RIPAS value
 * ret2 == RIPAS value
 */
#define SMC_RSI_IPA_STATE_GET		SMC64_RSI_FID(U(0x8))

/*
 * FID: 0xC4000199
 *
 * arg1 == IPA of the Host call data structure
 * ret0 == Status / error
 */
#define SMC_RSI_HOST_CALL		SMC64_RSI_FID(U(0x9))

/*
 * TODO: Update the documentation of new FIDs once the 1.1 spec has stabilized.
 */

/*
 * FID: 0xC400019A
 */
#define SMC_RSI_VSMMU_GET_INFO		SMC64_RSI_FID(U(0xA))

/*
 * FID: 0xC400019B
 */
#define SMC_RSI_ARCH_DEV_ACTIVATE	SMC64_RSI_FID(U(0xB))

/*
 * FID: 0xC400019C
 *
 * arg0 == Realm device identifier
 * arg1 == Flags
 * arg2 == Index of Plane whose stage 2 permissions are observed by non-ATS
 *         requests from the device
 * arg3 == Nonce generated on most recent transition to LOCKED state
 * arg4 == GET_MEASUREMENT request sequence number
 * arg5 == GET_INTERFACE_REPORT request sequence number
 */
#define SMC_RSI_VDEV_DMA_ENABLE		SMC64_RSI_FID(U(0xC))

/*
 * FID: 0xC400019D
 *
 * arg0 == Realm device identifier
 * arg1 == IPA to which the configuration data will be written
 */
#define SMC_RSI_VDEV_GET_INFO		SMC64_RSI_FID(U(0xD))

/*
 * FID: 0xC400019E is not used.
 */

/*
 * FID: 0xC400019F
 *
 * arg0 == Realm device identifier
 * arg1 == Base of target IPA region
 * arg2 == Top of target IPA region
 * arg3 == Base of target PA region
 * arg4 == Flags
 * arg5 == Nonce generated on most recent transition to LOCKED state
 * arg6 == GET_MEASUREMENT request sequence number
 * arg7 == GET_INTERFACE_REPORT request sequence number
 *
 * ret1 == Base of IPA region which was not modified by the command
 * ret2 == Whether the Host accepted or rejected the request
 */
#define SMC_RSI_VDEV_VALIDATE_MAPPING	SMC64_RSI_FID(U(0xF))

/*
 * FID: 0xC40001A0
 *
 * arg1 == Index of the plane to get values from
 * arg2 == Index of the permission to retrieve
 * ret0 == Status / error
 * ret1 == Memory permission value
 */
#define SMC_RSI_MEM_GET_PERM_VALUE	SMC64_RSI_FID(U(0x10))

/*
 * FID: 0xC40001A1
 *
 * arg1 == Base of target IPA region
 * arg2 == Top of target IPA region
 * arg3 == Permission index
 * arg4 == Cookie
 * ret0 == Status / error
 * ret1 == Base of IPA region which was not modified by the command
 * ret2 == RSI response. Whether the host accepted or rejected the request
 * ret3 == New cookie value
 */
#define SMC_RSI_MEM_SET_PERM_INDEX	SMC64_RSI_FID(U(0x11))

/*
 * FID: 0xC40001A2
 *
 * arg1 == Index of the plane where to modify the permissions
 * arg2 == Index of the permission to modify
 * arg3 == Memory permission value
 * ret0 == Status / error
 */
#define SMC_RSI_MEM_SET_PERM_VALUE	SMC64_RSI_FID(U(0x12))

/*
 * FID: 0xC40001A3
 *
 * arg1 == Index of target plane
 * arg2 == IPA of rsi_plane_run object
 * ret0 == Status / error
 */
#define SMC_RSI_PLANE_ENTER		SMC64_RSI_FID(U(0x13))

/*
 * FID: 0xC40001A4
 *
 * arg0 == Realm device identifier
 */
#define SMC_RSI_VDEV_DMA_DISABLE	SMC64_RSI_FID(U(0x14))

/*
 * FID: 0xC40001A5 - 0xC40001AD are not used.
 */

/*
 * FID: 0xC40001AE
 *
 * arg1 == Index of tharget plane
 * arg2 == Encoding of target register
 * ret0 == Status / error
 * ret1 == Read value
 */
#define SMC_RSI_PLANE_SYSREG_READ	SMC64_RSI_FID(U(0x1E))

/*
 * FID: 0xC40001AF
 *
 * arg1 == Index of target plane
 * arg2 == Encoding of target register
 * arg3 == Value to write to target register
 * ret0 == Status / error
 */
#define SMC_RSI_PLANE_SYSREG_WRITE	SMC64_RSI_FID(U(0x1F))

/*
 * TODO: Currently RMM do not have support to enable RSI commands above FID
 * 0xC40001AF as this conflicts with RMM EL3 interface FIDs. Once RMM needs to
 * supports these RSI commands (mainly related to P2P device communication) the
 * RMM EL3 interface FIDs range will be changed.
 */

/*
 * FID: 0xC40001BF
 */
#define SMC_RDEV_P2P_BIND		SMC64_RSI_FID(U(0x2F))

/* Number of general purpose registers per Plane */
#define RSI_PLANE_NR_GPRS		U(31)

/* Maximum number of Interrupt Controller List Registers */
#define RSI_PLANE_GIC_NUM_LRS		U(16)

/* RsiPlaneExitReason represents the reason for a Plane exit */
#define RSI_EXIT_SYNC			U(0)
#define RSI_EXIT_IRQ			U(1)
#define RSI_EXIT_HOST			U(2)

/*
 * RsiPlaneEnterFlags
 *
 * Flags provided by Plane 0 to RMM to configure entry into Plane N.
 */
#define RSI_PLANE_ENTER_FLAGS_TRAP_WFI	U(1UL << 0)
#define RSI_PLANE_ENTER_FLAGS_TRAP_WFE	U(1UL << 1)
#define RSI_PLANE_ENTER_FLAGS_TRAP_HC	U(1UL << 2)
#define RSI_PLANE_ENTER_FLAGS_OWN_GIC	U(1UL << 3)
#define RSI_PLANE_ENTER_FLAGS_TRAP_SIMD	U(1UL << 4)

/*
 * Possible values for RsiTrap type *
 */
#define RSI_TRAP			(1UL)
#define RSI_NO_TRAP			(0UL)

#ifndef __ASSEMBLER__
/*
 * Defines member of structure and reserves space
 * for the next member with specified offset.
 */
#define SET_MEMBER_RSI	SET_MEMBER

/* Size of Realm Personalization Value */
#ifndef CBMC
#define RSI_RPV_SIZE		64
#else
/*
 * Small RPV size so that RsiRealmConfig structure
 * fits in the reduced sized granule defined for CBMC
 */
#define RSI_RPV_SIZE		1
#endif

/* RsiRealmConfig structure containing realm configuration */
struct rsi_realm_config {
	/* IPA width in bits */
	SET_MEMBER_RSI(unsigned long ipa_width, 0, 8);			/* Offset 0 */
	/* Hash algorithm */
	SET_MEMBER_RSI(unsigned char algorithm, 8, 0x10);		/* Offset 8 */
	/* Number of auxiliary Planes */
	SET_MEMBER_RSI(unsigned long num_aux_planes, 0x10, 0x18);	/* Offset 0x10 */
	/* GICv3 VGIC Type Register value */
	SET_MEMBER_RSI(unsigned int gicv3_vtr, 0x18, 0x20);		/* Offset 0x12 */
	/*
	 * If ATS is enabled, determines the stage 2 translation used by devices
	 * assigned to the Realm
	 */
	SET_MEMBER_RSI(unsigned long ats_plane, 0x20, 0x200);		/* Offset 0x20 */

	/* Realm Personalization Value */
	SET_MEMBER_RSI(unsigned char rpv[RSI_RPV_SIZE], 0x200, 0x1000);
};

#define RSI_HOST_CALL_NR_GPRS		U(31)

struct rsi_host_call {
	SET_MEMBER_RSI(struct {
		/* Immediate value */
		unsigned int imm;		/* Offset 0 */
		/* Registers */
		unsigned long gprs[RSI_HOST_CALL_NR_GPRS];
		}, 0, 0x100);
};

/*
 * RsiFeature
 * Represents whether a feature is enabled.
 * Width: 1 bit
 */
#define RSI_FEATURE_FALSE			U(0)
#define RSI_FEATURE_TRUE			U(1)

/*
 * RsiFeatureRegister0
 * Fieldset contains feature register 0
 * Width: 64 bits
 */
#define RSI_FEATURE_REGISTER_0_INDEX		UL(0)
#define RSI_FEATURE_REGISTER_0_DA_SHIFT		UL(0)
#define RSI_FEATURE_REGISTER_0_DA_WIDTH		UL(1)
#define RSI_FEATURE_REGISTER_0_MRO_SHIFT	UL(1)
#define RSI_FEATURE_REGISTER_0_MRO_WIDTH	UL(1)
#define RSI_FEATURE_REGISTER_0_ATS_SHIFT	UL(2)
#define RSI_FEATURE_REGISTER_0_ATS_WIDTH	UL(1)

/*
 * RsiDevMemShared
 * Represents whether an device memory mapping is shared.
 * Width: 1 bit
 */
#define RSI_DEV_MEM_MAPPING_PRIVATE		U(0)
#define RSI_DEV_MEM_MAPPING_SHARED		U(1)

/*
 * RsiDevMemCoherent
 * Represents whether a device memory location is within the system coherent
 * memory space.
 * Width: 1 bit
 */
#define RSI_DEV_MEM_NON_COHERENT		U(0)
#define RSI_DEV_MEM_COHERENT			U(1)

/*
 * RsiRdevValidateIoFlags
 * Fieldset contains flags provided when requesting validation of an IO mapping.
 * Width: 64 bits
 */
/* RsiDevMemShared: Bits 0 to 1 */
#define RSI_RDEV_VALIDATE_IO_FLAGS_SHARE_SHIFT	UL(0)
#define RSI_RDEV_VALIDATE_IO_FLAGS_SHARE_WIDTH	UL(1)
/* RsiDevMemCoherent: Bits 1 to 2 */
#define RSI_RDEV_VALIDATE_IO_FLAGS_COH_SHIFT	UL(1)
#define RSI_RDEV_VALIDATE_IO_FLAGS_COH_WIDTH	UL(1)

/*
 * RsiVdevState
 * This enumeration represents the state of a VDEV.
 * Width: 8 bits.
 */
#define RSI_VDEV_STATE_UNLOCKED			((unsigned char)0)
#define RSI_VDEV_STATE_LOCKED			((unsigned char)1)
#define RSI_VDEV_STATE_STARTED			((unsigned char)2)
#define RSI_VDEV_STATE_ERROR			((unsigned char)3)

/*
 * RsiDevFlags
 * Fieldset contains flags which describe properties of a device.
 * Width: 64 bits
 */
#define RSI_DEV_FLAGS_P2P_SHIFT			UL(0)
#define RSI_DEV_FLAGS_P2P_WIDTH			UL(1)

/*
 * RsiSysregAddress type definitons.
 *
 * The field encodings use the same shifts as used by KVM, that is, OP2
 * starts at offset 0 (as Rt field on MSR/MRS instructions OPCODE is ignored),
 * so we can reuse the existing macros as long as we set the op2 shift as 0.
 */
#define RSI_SYSREG_ADDR_KVM_OP2_SHIFT		(U(0))
#define RSI_SYSREG_ADDR_KVM_OP2_WIDTH		(EL2_SYSREG_ACCESS_OP2_WIDTH)

#define RSI_SYSREG_ADDR_KVM_CRM_SHIFT		((RSI_SYSREG_ADDR_KVM_OP2_SHIFT) +	\
						 (RSI_SYSREG_ADDR_KVM_OP2_WIDTH))
#define RSI_SYSREG_ADDR_KVM_CRM_WIDTH		(EL2_SYSREG_ACCESS_CRM_WIDTH)

#define RSI_SYSREG_ADDR_KVM_CRN_SHIFT		((RSI_SYSREG_ADDR_KVM_CRM_SHIFT) +	\
						 (RSI_SYSREG_ADDR_KVM_CRM_WIDTH))
#define RSI_SYSREG_ADDR_KVM_CRN_WIDTH		(EL2_SYSREG_ACCESS_CRN_WIDTH)

#define RSI_SYSREG_ADDR_KVM_OP1_SHIFT		((RSI_SYSREG_ADDR_KVM_CRN_SHIFT) +	\
						 (RSI_SYSREG_ADDR_KVM_CRN_WIDTH))
#define RSI_SYSREG_ADDR_KVM_OP1_WIDTH		(EL2_SYSREG_ACCESS_OP1_WIDTH)

#define RSI_SYSREG_ADDR_KVM_OP0_SHIFT		((RSI_SYSREG_ADDR_KVM_OP1_SHIFT) +	\
						 (RSI_SYSREG_ADDR_KVM_OP1_WIDTH))
#define RSI_SYSREG_ADDR_KVM_OP0_WIDTH		(EL2_SYSREG_ACCESS_OP0_WIDTH)

#define RSI_SYSREG_ADDR_KVM_SYSREG128_SHIFT	((RSI_SYSREG_ADDR_KVM_OP0_SHIFT) +	\
						 (RSI_SYSREG_ADDR_KVM_OP0_WIDTH))
#define RSI_SYSREG_ADDR_KVM_SYSREG128_WIDTH	(U(1))

#define RSI_SYSREG_ADDR_KVM_OPCODE(op0, op1, crn, crm, op2)	\
	((UL(op0) << RSI_SYSREG_ADDR_KVM_OP0_SHIFT) |		\
	 (UL(op1) << RSI_SYSREG_ADDR_KVM_OP1_SHIFT) |		\
	 (UL(crn) << RSI_SYSREG_ADDR_KVM_CRN_SHIFT) |		\
	 (UL(crm) << RSI_SYSREG_ADDR_KVM_CRM_SHIFT) |		\
	 (UL(op2) << RSI_SYSREG_ADDR_KVM_OP2_SHIFT))

/******************************************************************************
 * Definitions of system register identifiers supported by
 * RSI_PLANE_SYSREG_{READ, WRITE}
 *
 * Note that the register IDs generated match the KVM format.
 *****************************************************************************/

#define RSI_SYSREG_KVM_ID_actlr_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 1, 0, 1)
#define RSI_SYSREG_KVM_ID_afsr0_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 5, 1, 0)
#define RSI_SYSREG_KVM_ID_afsr1_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 5, 1, 1)
#define RSI_SYSREG_KVM_ID_amair_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 10, 3, 0)
#define RSI_SYSREG_KVM_ID_apiakeylo_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 2, 1, 0)
#define RSI_SYSREG_KVM_ID_apiakeyhi_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 2, 1, 1)
#define RSI_SYSREG_KVM_ID_apibkeylo_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 2, 1, 2)
#define RSI_SYSREG_KVM_ID_apibkeyhi_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 2, 1, 3)
#define RSI_SYSREG_KVM_ID_apdakeylo_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 2, 2, 0)
#define RSI_SYSREG_KVM_ID_apdakeyhi_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 2, 2, 1)
#define RSI_SYSREG_KVM_ID_apdbkeylo_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 2, 2, 2)
#define RSI_SYSREG_KVM_ID_apdbkeyhi_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 2, 2, 3)
#define RSI_SYSREG_KVM_ID_apgakeylo_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 2, 3, 0)
#define RSI_SYSREG_KVM_ID_apgakeyhi_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 2, 3, 1)
#define RSI_SYSREG_KVM_ID_cntkctl_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 14, 1, 0)
#define RSI_SYSREG_KVM_ID_contextidr_el1	RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 13, 0, 1)
#define RSI_SYSREG_KVM_ID_cpacr_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 1, 0, 2)
#define RSI_SYSREG_KVM_ID_csselr_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 2, 0, 0, 0)
#define RSI_SYSREG_KVM_ID_disr_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 12, 1, 1)
#define RSI_SYSREG_KVM_ID_elr_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 4, 0, 1)
#define RSI_SYSREG_KVM_ID_esr_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 5, 2, 0)
#define RSI_SYSREG_KVM_ID_far_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 6, 0, 0)
#define RSI_SYSREG_KVM_ID_mair_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 10, 2, 0)
#define RSI_SYSREG_KVM_ID_mdccint_el1		RSI_SYSREG_ADDR_KVM_OPCODE(2, 0, 0, 2, 0)
#define RSI_SYSREG_KVM_ID_mdscr_el1		RSI_SYSREG_ADDR_KVM_OPCODE(2, 0, 0, 2, 2)
#define RSI_SYSREG_KVM_ID_par_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 7, 4, 0)
#define RSI_SYSREG_KVM_ID_sctlr_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 1, 0, 0)
#define RSI_SYSREG_KVM_ID_sp_el0		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 4, 1, 0)
#define RSI_SYSREG_KVM_ID_sp_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 4, 4, 1, 0)
#define RSI_SYSREG_KVM_ID_spsr_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 4, 0, 0)
#define RSI_SYSREG_KVM_ID_tcr_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 2, 0, 2)
#define RSI_SYSREG_KVM_ID_tpidr_el0		RSI_SYSREG_ADDR_KVM_OPCODE(3, 3, 13, 0, 2)
#define RSI_SYSREG_KVM_ID_tpidr_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 13, 0, 4)
#define RSI_SYSREG_KVM_ID_tpidrro_el0		RSI_SYSREG_ADDR_KVM_OPCODE(3, 3, 13, 0, 3)
#define RSI_SYSREG_KVM_ID_ttbr0_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 2, 0, 0)
#define RSI_SYSREG_KVM_ID_ttbr1_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 2, 0, 1)
#define RSI_SYSREG_KVM_ID_vbar_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 12, 0, 0)
#define RSI_SYSREG_KVM_ID_zcr_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 1, 2, 0)
#define RSI_SYSREG_KVM_ID_cntp_ctl_el0		RSI_SYSREG_ADDR_KVM_OPCODE(3, 3, 14, 2, 1)
#define RSI_SYSREG_KVM_ID_cntp_cval_el0		RSI_SYSREG_ADDR_KVM_OPCODE(3, 3, 14, 2, 2)
#define RSI_SYSREG_KVM_ID_cntv_ctl_el0		RSI_SYSREG_ADDR_KVM_OPCODE(3, 3, 14, 3, 1)
#define RSI_SYSREG_KVM_ID_cntv_cval_el0		RSI_SYSREG_ADDR_KVM_OPCODE(3, 3, 14, 3, 2)
#define RSI_SYSREG_KVM_ID_brbcr_el1		RSI_SYSREG_ADDR_KVM_OPCODE(2, 1, 9, 0, 0)
#define RSI_SYSREG_KVM_ID_tcr2_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 2, 0, 3)
#define RSI_SYSREG_KVM_ID_pir_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 10, 2, 3)
#define RSI_SYSREG_KVM_ID_pire0_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 10, 2, 2)
#define RSI_SYSREG_KVM_ID_por_el1		RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 10, 2, 4)

#define RSI_SYSREG_KVM_ID_pmcr_el0		RSI_SYSREG_ADDR_KVM_OPCODE(3, 3, 9, 12, 0)
#define RSI_SYSREG_KVM_ID_pmccfiltr_el0		RSI_SYSREG_ADDR_KVM_OPCODE(3, 3, 14, 15, 7)
#define RSI_SYSREG_KVM_ID_pmccntr_el0		RSI_SYSREG_ADDR_KVM_OPCODE(3, 3, 9, 13, 0)
#define RSI_SYSREG_KVM_ID_pmcntenset_el0	RSI_SYSREG_ADDR_KVM_OPCODE(3, 3, 9, 12, 1)
#define RSI_SYSREG_KVM_ID_pmintenset_el1	RSI_SYSREG_ADDR_KVM_OPCODE(3, 0, 9, 14, 1)
#define RSI_SYSREG_KVM_ID_pmovsset_el0		RSI_SYSREG_ADDR_KVM_OPCODE(3, 3, 9, 14, 3)
#define RSI_SYSREG_KVM_ID_pmselr_el0		RSI_SYSREG_ADDR_KVM_OPCODE(3, 3, 9, 12, 5)
#define RSI_SYSREG_KVM_ID_pmuserenr_el0		RSI_SYSREG_ADDR_KVM_OPCODE(3, 3, 9, 14, 0)

#define RSI_SYSREG_PMEV_MASK			RSI_SYSREG_ADDR_KVM_OPCODE(3, 7, 15, 12, 0)
#define RSI_SYSREG_PMEVCNTR_MASK		RSI_SYSREG_ADDR_KVM_OPCODE(3, 3, 14, 8, 0)
#define RSI_SYSREG_PMEVTYPER_MASK		RSI_SYSREG_ADDR_KVM_OPCODE(3, 3, 14, 12, 0)

#define RSI_VDEV_VCA_DIGEST_LEN			U(64)
#define RSI_VDEV_CERT_DIGEST_LEN		U(64)
#define RSI_VDEV_PUBKEY_DIGEST_LEN		U(64)
#define RSI_VDEV_MEAS_DIGEST_LEN		U(64)
#define RSI_VDEV_REPORT_DIGEST_LEN		U(64)

/*
 * RsiVdevFlags
 * Contains flags which describe properties of a device.
 * Width: 8 bytes
 */
#define RSI_VDEV_FLAGS_P2P_ENABLED_SHIFT	U(0)
#define RSI_VDEV_FLAGS_P2P_ENABLED_WIDTH	U(1)
#define RSI_VDEV_FLAGS_P2P_BOUND_SHIFT		U(1)
#define RSI_VDEV_FLAGS_P2P_BOUND_WIDTH		U(1)
#define RSI_VDEV_FLAGS_VSMMU_SHIFT		U(2)
#define RSI_VDEV_FLAGS_VSMMU_WIDTH		U(1)

/*
 * RsiVdevInfo
 * Contains device configuration information.
 * Width: 512 (0x200) bytes.
 */
/* cppcheck-suppress misra-c2012-2.4 */
struct rsi_vdev_info {
	/* RsiDevFlags: Flags */
	SET_MEMBER_RSI(unsigned long flags, 0, 0x8);
	/* UInt64: cert_id*/
	SET_MEMBER_RSI(unsigned long cert_id, 0x8, 0x10);
	/* RsiHashAlgorithm: Algorithm used to generate device digests */
	SET_MEMBER_RSI(unsigned char hash_algo, 0x10, 0x18);
	/* UInt64: Nonce generated on most recent transition to LOCKED state */
	SET_MEMBER_RSI(unsigned long lock_nonce, 0x18, 0x20);
	/* UInt64: Nonce generated on most recent GET_MEASUREMENT request */
	SET_MEMBER_RSI(unsigned long meas_nonce, 0x20, 0x28);
	/* UInt64: Nonce generated on most recent GET_INTERFACE_REPORT request */
	SET_MEMBER_RSI(unsigned long report_nonce, 0x28, 0x30);
	/* UInt64: TDISP version of the device */
	SET_MEMBER_RSI(unsigned long tdisp_version, 0x30, 0x38);
	/* RsiVdevState: State of the device */
	SET_MEMBER_RSI(unsigned char state, 0x38, 0x40);
	/* Bits512: VCA digest */
	SET_MEMBER_RSI(unsigned char vca_digest[RSI_VDEV_VCA_DIGEST_LEN], 0x40, 0x80);
	/* Bits512: Certificate digest */
	SET_MEMBER_RSI(unsigned char cert_digest[RSI_VDEV_CERT_DIGEST_LEN], 0x80, 0xc0);
	/* Bits512: Public key digest */
	SET_MEMBER_RSI(unsigned char pubkey_digest[RSI_VDEV_PUBKEY_DIGEST_LEN], 0xc0, 0x100);
	/* Bits512: Measurement digest */
	SET_MEMBER_RSI(unsigned char meas_digest[RSI_VDEV_MEAS_DIGEST_LEN], 0x100, 0x140);
	/* Bits512: Interface report digest */
	SET_MEMBER_RSI(unsigned char report_digest[RSI_VDEV_REPORT_DIGEST_LEN], 0x140, 0x180);
	/*
	 * Address: Base IPA of the VSMMU which is associated with this device.
	 * This field is valid only if flags.vsmmu == RSI_FEATURE_TRUE.
	 */
	SET_MEMBER_RSI(unsigned long vsmmu_addr, 0x180, 0x188);
	/*
	 * UInt64: Virtual Stream ID.
	 * This field is valid only if flags.vsmmu == RSI_FEATURE_TRUE.
	 */
	SET_MEMBER_RSI(unsigned long vsmmu_vsid, 0x188, 0x200);
};

/* Returns the higher supported RSI ABI revision */
unsigned long rsi_get_highest_supported_version(void);

/*
 * Data passed from Plane 0 to the RMM on entry to Plane N.
 */
struct rsi_plane_enter {
	/* RsiPlaneEnterFlags - Offset 0x0 */
	SET_MEMBER_RSI(unsigned long flags, 0, 0x8);
	/* Program counter - Offset 0x8 */
	SET_MEMBER_RSI(unsigned long pc, 0x8, 0x10);
	/* PSTATE_value  - Offset 0x10 */
	SET_MEMBER_RSI(unsigned long pstate, 0x10, 0x100);
	/* General purpose registers - Offset 0x100 */
	SET_MEMBER_RSI(unsigned long gprs[RSI_PLANE_NR_GPRS], 0x100, 0x200);
	/* GICv3 registers */
	SET_MEMBER_RSI(
		struct {
			/* GICv3 Hypervisor Control Register - Offset 0x200 */
			unsigned long gicv3_hcr;
			/* GICv3 List Registers - Offset 0x208 */
			unsigned long gicv3_lrs[RSI_PLANE_GIC_NUM_LRS];
		}, 0x200, 0x300);
};

/*
 * Data passed from the RMM to Plane 0 on exit from Plane N.
 */
struct rsi_plane_exit {
	/* RsiPlaneExitReason - Offset 0x0 */
	SET_MEMBER_RSI(unsigned long reason, 0x0, 0x100);
	/* EL2 system registers */
	SET_MEMBER_RSI(
		struct {
			/* Exception Link Register - Offset 0x100 */
			unsigned long elr_el2;
			/* Exception Syndrome Register - Offset 0x108 */
			unsigned long esr_el2;
			/* Fault Address Register - Offset 0x110 */
			unsigned long far_el2;
			/* Hypervisor IPA Fault Address register - Offset 0x118 */
			unsigned long hpfar_el2;
			/* PSTATE Value - Offset 0x120 */
			unsigned long pstate;
		}, 0x100, 0x200);
	/* General purpose registers - Offset 0x200 */
	SET_MEMBER_RSI(unsigned long gprs[RSI_PLANE_NR_GPRS], 0x200, 0x300);
	/* GICv3 registers */
	SET_MEMBER_RSI(
		struct {
			/* GICv3 Hypervisor Control Register - Offset 0x300 */
			unsigned long gicv3_hcr;
			/* GICv3 List Registers - Offset 0x308 */
			unsigned long gicv3_lrs[RSI_PLANE_GIC_NUM_LRS];
			/* GICv3 Maintenance Interrupt State Register - Offset 0x388 */
			unsigned long gicv3_misr;
			/* GICv3 Virtual Machine Control Register - Offset 0x390*/
			unsigned long gicv3_vmcr;
		}, 0x300, 0x400);
	/* Timer registers */
	SET_MEMBER_RSI(
		struct {
			/* Physical Timer Control Register Value - Offstet 0x400 */
			unsigned long cntp_ctl;
			/* Physical Timer Compare Value Register - Offset 0x408 */
			unsigned long cntp_cval;
			/* Virtual Timer Control Register Value - Offset 0x410 */
			unsigned long cntv_ctl;
			/* Virtual Timer Compare Value Register - Offset 0x418 */
			unsigned long cntv_cval;
		}, 0x400, 0x500);
};

/*
 * Data shared between Plane 0 and the RMM during entry to and exit
 * from Plane N.
 */
struct rsi_plane_run {
	/* Entry information - Offset 0x0 */
	SET_MEMBER_RSI(struct rsi_plane_enter enter, 0x0, 0x800);
	/* Exit information - Offset 0x800 */
	SET_MEMBER_RSI(struct rsi_plane_exit exit, 0x800, 0x1000);
};

#endif /* __ASSEMBLER__ */

#endif /* SMC_RSI_H */

/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SMC_RSI_H
#define SMC_RSI_H

#include <smc.h>

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
#define SMC_RSI_VSMMU_ACTIVATE		SMC64_RSI_FID(U(0xB))

/*
 * FID: 0xC400019C
 */
#define SMC_RSI_RDEV_GET_INSTANCE_ID	SMC64_RSI_FID(U(0xC))

/*
 * FID: 0xC400019D - 0xC400019F are not used.
 */

/*
 * FID: 0xC40001A0
 */
#define SMC_RSI_MEM_GET_PERM_VALUE	SMC64_RSI_FID(U(0x10))

/*
 * FID: 0xC40001A1
 */
#define SMC_RSI_MEM_SET_PERM_INDEX	SMC64_RSI_FID(U(0x11))

/*
 * FID: 0xC40001A2
 */
#define SMC_RSI_MEM_SET_PERM_VALUE	SMC64_RSI_FID(U(0x12))

/*
 * FID: 0xC40001A3
 */
#define SMC_RSI_PLANE_ENTER		SMC64_RSI_FID(U(0x13))

/*
 * FID: 0xC40001A4
 */
#define SMC_RSI_RDEV_CONTINUE		SMC64_RSI_FID(U(0x14))

/*
 * FID: 0xC40001A5
 */
#define SMC_RSI_RDEV_GET_INFO		SMC64_RSI_FID(U(0x15))

/*
 * FID: 0xC40001A6
 */
#define SMC_RSI_RDEV_GET_INTERFACE_REPORT SMC64_RSI_FID(U(0x16))

/*
 * FID: 0xC40001A7
 */
#define SMC_RSI_RDEV_GET_MEASUREMENTS	SMC64_RSI_FID(U(0x17))

/*
 * FID: 0xC40001A8
 */
#define SMC_RSI_RDEV_GET_STATE		SMC64_RSI_FID(U(0x18))

/*
 * FID: 0xC40001A9
 */
#define SMC_RSI_RDEV_LOCK		SMC64_RSI_FID(U(0x19))

/*
 * FID: 0xC40001AA
 */
#define SMC_RSI_RDEV_START		SMC64_RSI_FID(U(0x1A))

/*
 * FID: 0xC40001AB
 */
#define SMC_RSI_RDEV_STOP		SMC64_RSI_FID(U(0x1B))

/*
 * FID: 0xC40001AC
 */
#define SMC_RSI_RDEV_VALIDATE_MAPPING	SMC64_RSI_FID(U(0x1C))

/*
 * FID: 0xC40001AD is not used.
 */

/*
 * FID: 0xC40001AE
 */
#define SMC_RSI_PLANE_REG_READ		SMC64_RSI_FID(U(0x1E))

/*
 * FID: 0xC40001AF
 */
#define SMC_RSI_PLANE_REG_WRITE		SMC64_RSI_FID(U(0x1F))

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
	SET_MEMBER_RSI(unsigned long ipa_width, 0, 8);
	/* Hash algorithm */
	SET_MEMBER_RSI(unsigned char algorithm, 0x8, 0x10);
	/* Number of auxiliary Planes */
	SET_MEMBER_RSI(unsigned long num_aux_planes, 0x10, 0x18);
	/* GICv3 VGIC Type Register value */
	SET_MEMBER_RSI(unsigned long gicv3_vtr, 0x18, 0x20);
	/*
	 * If ATS is enabled, determines the stage 2 translation used by devices
	 * assigned to the Realm
	 */
	SET_MEMBER_RSI(unsigned long ats_plane, 0x20, 0x200);

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
 * RsiDeviceState
 * This enumeration represents state of an assigned Realm device.
 * Width: 64 bits.
 */
#define RSI_RDEV_STATE_UNLOCKED			U(0)
#define RSI_RDEV_STATE_UNLOCKED_BUSY		U(1)
#define RSI_RDEV_STATE_LOCKED			U(2)
#define RSI_RDEV_STATE_LOCKED_BUSY		U(3)
#define RSI_RDEV_STATE_STARTED			U(4)
#define RSI_RDEV_STATE_STARTED_BUSY		U(5)
#define RSI_RDEV_STATE_STOPPING			U(6)
#define RSI_RDEV_STATE_STOPPED			U(7) /* unused will be removed */
#define RSI_RDEV_STATE_ERROR			U(8)

/*
 * RsiDevFlags
 * Fieldset contains flags which describe properties of a device.
 * Width: 64 bits
 */
#define RSI_DEV_FLAGS_P2P_SHIFT			UL(0)
#define RSI_DEV_FLAGS_P2P_WIDTH			UL(1)

/*
 * RsiDevAttestType
 * This enumeration represents attestation type of a device.
 * Width: 64 bits.
 */
#define RSI_DEV_ATTEST_TYPE_INDEPENDENTLY_ATTESTED	U(0)
#define RSI_DEV_ATTEST_TYPE_PLATFORM_ATTESTED		U(1)

/*
 * RsiDevInfo
 * Contains device configuration information.
 * Width: 512 (0x200) bytes.
 */
struct rsi_dev_info {
	/* RsiDevFlags: Flags */
	SET_MEMBER_RSI(unsigned long flags, 0, 0x8);
	/* RsiDevAttestType: Attestation type */
	SET_MEMBER_RSI(unsigned long attest_type, 0x8, 0x10);
	/* UInt64: Certificate identifier */
	SET_MEMBER_RSI(unsigned long cert_id, 0x10, 0x18);
	/* RsiHashAlgorithm: Algorithm used to generate device digests */
	SET_MEMBER_RSI(unsigned char hash_algo, 0x18, 0x40);

	/* Bits512: Certificate digest */
	SET_MEMBER_RSI(unsigned char cert_digest[64], 0x40, 0x80);
	/* Bits512: Measurement block digest */
	SET_MEMBER_RSI(unsigned char meas_digest[64], 0x80, 0xc0);
	/* Bits512: Interface report digest */
	SET_MEMBER_RSI(unsigned char report_digest[64], 0xc0, 0x200);
};

/*
 * RsiDevMeasureAll
 * Represents whether all device measurements should be returned.
 * Width: 1 bit
 */
#define RSI_DEV_MEASURE_NOT_ALL			U(0)
#define RSI_DEV_MEASURE_ALL			U(1)

/*
 * RsiDevMeasureSigned
 * Represents whether a device measurement is signed.
 * Width: 1 bit
 */
#define RSI_DEV_MEASURE_NOT_SIGNED		U(0)
#define RSI_DEV_MEASURE_SIGNED			U(1)

/*
 * RsiDevMeasureRaw
 * Represents whether a device measurement is a raw bitstream.
 * Width: 1 bit
 */
#define RSI_DEV_MEASURE_NOT_RAW			U(0)
#define RSI_DEV_MEASURE_RAW			U(1)

/*
 * RsiDevMeasureFlags
 * Fieldset contains flags which describe properties of device measurements.
 * Width: 64 bits
 */
/* RsiDevMeasureAll */
#define RSI_DEV_MEASURE_FLAGS_ALL_SHIFT		U(0)
#define RSI_DEV_MEASURE_FLAGS_ALL_WIDTH		U(1)
/* RsiDevMeasureSigned */
#define RSI_DEV_MEASURE_FLAGS_SIGNED_SHIFT	U(1)
#define RSI_DEV_MEASURE_FLAGS_SIGNED_WIDTH	U(1)
/* RsiDevMeasureRaw */
#define RSI_DEV_MEASURE_FLAGS_RAW_SHIFT		U(2)
#define RSI_DEV_MEASURE_FLAGS_RAW_WIDTH		U(1)

/*
 * RsiDevMeasureParams
 * This structure contains device measurement parameters.
 * Width: 4096 (0x1000) bytes.
 */
struct rsi_dev_measure_params {
	/* RsiDevMeasureFlags: Properties of device measurements */
	SET_MEMBER_RSI(unsigned long flags, 0, 0x8);

	/* RsiBoolean[256]: Measurement indices */
	SET_MEMBER_RSI(unsigned char indices[32], 0x100, 0x200);
	/* RsiBoolean[256]: Nonce value used in measurement requests */
	SET_MEMBER_RSI(unsigned char nonce[32], 0x200, 0x1000);
};

/* Returns the higher supported RSI ABI revision */
unsigned long rsi_get_highest_supported_version(void);
#endif /* __ASSEMBLER__ */

#endif /* SMC_RSI_H */

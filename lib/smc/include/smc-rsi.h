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

/*
 * The major version number of the RSI implementation.  Increase this whenever
 * the binary format or semantics of the SMC calls change.
 */
#define RSI_ABI_VERSION_MAJOR		UL(14)

/*
 * The minor version number of the RSI implementation.  Increase this when
 * a bug is fixed, or a feature is added without breaking binary compatibility.
 */
#define RSI_ABI_VERSION_MINOR		UL(0)

#define RSI_ABI_VERSION			((RSI_ABI_VERSION_MAJOR << U(16)) | \
					  RSI_ABI_VERSION_MINOR)

#define RSI_ABI_VERSION_GET_MAJOR(_version) ((_version) >> U(16))
#define RSI_ABI_VERSION_GET_MINOR(_version) ((_version) & U(0xFFFF))

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

#define RSI_ERROR_COUNT		UL(4)

/* RsiHashAlgorithm */
#define RSI_HASH_SHA_256	U(0)
#define RSI_HASH_SHA_512	U(1)

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
 * Returns RSI version.
 * arg1: Requested interface version
 * ret0: Status / error
 * ret1: Implemented interface version
 */
#define SMC_RSI_ABI_VERSION		SMC64_RSI_FID(U(0x0))

/*
 * Returns RSI version.
 * arg1: Feature register index
 * ret0: Status / error
 * ret1: Feature register value
 */
#define SMC_RSI_FEATURES		SMC64_RSI_FID(U(0x1))

/*
 * Returns a measurement.
 * arg1: Measurement index (0..4), measurement (RIM or REM) to read
 * ret0: Status / error
 * ret1: Measurement value, bytes:  0 -  7
 * ret2: Measurement value, bytes:  7 - 15
 * ret3: Measurement value, bytes: 16 - 23
 * ret4: Measurement value, bytes: 24 - 31
 * ret5: Measurement value, bytes: 32 - 39
 * ret6: Measurement value, bytes: 40 - 47
 * ret7: Measurement value, bytes: 48 - 55
 * ret8: Measurement value, bytes: 56 - 63
 */
#define SMC_RSI_MEASUREMENT_READ	SMC64_RSI_FID(U(0x2))

/*
 * Extends a REM.
 * arg0:  Measurement index (1..4), measurement (REM) to extend
 * arg1:  Measurement size in bytes
 * arg3:  Challenge value, bytes:  0 -  7
 * arg4:  Challenge value, bytes:  7 - 15
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
 * Initialize the operation to retrieve an attestation token.
 * arg1: The IPA of token buffer
 * arg2: Challenge value, bytes:  0 -  7
 * arg3: Challenge value, bytes:  7 - 15
 * arg4: Challenge value, bytes: 16 - 23
 * arg5: Challenge value, bytes: 24 - 31
 * arg6: Challenge value, bytes: 32 - 39
 * arg7: Challenge value, bytes: 40 - 47
 * arg8: Challenge value, bytes: 48 - 55
 * arg9: Challenge value, bytes: 56 - 63
 * ret0: Status / error
 * ret1: Size of completed token in bytes
 */
#define SMC_RSI_ATTEST_TOKEN_INIT	SMC64_RSI_FID(U(0x4))

/*
 * Continue the operation to retrieve an attestation token.
 * arg1: The IPA of token buffer
 * ret0: Status / error
 * ret1: Size of completed token in bytes
 */
#define SMC_RSI_ATTEST_TOKEN_CONTINUE	SMC64_RSI_FID(U(0x5))

#ifndef __ASSEMBLER__
/*
 * Defines member of structure and reserves space
 * for the next member with specified offset.
 */
#define SET_MEMBER_RSI	SET_MEMBER

/* RsiRealmConfig structure containing realm configuration */
struct rsi_realm_config {
	/* IPA width in bits */
	SET_MEMBER_RSI(unsigned long ipa_width, 0, 8);		/* Offset 0 */
	/* Hash algorithm */
	SET_MEMBER_RSI(unsigned long algorithm, 8, 0x1000);	/* Offset 8 */
};

#endif /* __ASSEMBLER__ */

/*
 * arg0 == struct rsi_realm_config address
 */
#define SMC_RSI_REALM_CONFIG		SMC64_RSI_FID(U(0x6))

/*
 * arg0 == Base IPA address of target region
 * arg1 == Top address of target region
 * arg2 == RIPAS value
 * arg3 == flags
 * ret0 == Status / error
 * ret1 == Top of modified IPA range
 */
#define SMC_RSI_IPA_STATE_SET		SMC64_RSI_FID(U(0x7))

/*
 * arg0 == IPA
 * ret0 == Status / error
 * ret1 == RIPAS value
 */
#define SMC_RSI_IPA_STATE_GET		SMC64_RSI_FID(U(0x8))

#define RSI_HOST_CALL_NR_GPRS		U(31)

#ifndef __ASSEMBLER__
struct rsi_host_call {
	SET_MEMBER_RSI(struct {
		/* Immediate value */
		unsigned int imm;		/* Offset 0 */
		/* Registers */
		unsigned long gprs[RSI_HOST_CALL_NR_GPRS];
		}, 0, 0x100);
};

#endif /* __ASSEMBLER__ */

/*
 * arg0 == struct rsi_host_call address
 */
#define SMC_RSI_HOST_CALL		SMC64_RSI_FID(U(0x9))

#endif /* SMC_RSI_H */
